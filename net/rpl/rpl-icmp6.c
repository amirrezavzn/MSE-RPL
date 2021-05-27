/*
 * Copyright (c) 2010, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 */

/**
 * \file
 *         ICMP6 I/O for RPL control messages.
 *
 * \author Joakim Eriksson <joakime@sics.se>, Nicolas Tsiftes <nvt@sics.se>
 * Contributors: Niclas Finne <nfi@sics.se>, Joel Hoglund <joel@sics.se>,
 *               Mathieu Pouillot <m.pouillot@watteco.com>
 *               George Oikonomou <oikonomou@users.sourceforge.net> (multicast)
 */

/**
 * \addtogroup uip6
 * @{
 */

#include "net/ip/tcpip.h"
#include "net/ip/uip.h"
#include "net/ipv6/uip-ds6.h"
#include "net/ipv6/uip-nd6.h"
#include "net/ipv6/uip-icmp6.h"
#include "net/rpl/rpl-private.h"
#include "net/packetbuf.h"
#include "net/ipv6/multicast/uip-mcast6.h"

#include <limits.h>
#include <string.h>
//Amirreza :
#include "cc2420.h"
#include "rpl.h"

#define DEBUG DEBUG_NONE

#include "net/ip/uip-debug.h"

/*---------------------------------------------------------------------------*/
#define RPL_DIO_GROUNDED                 0x80
#define RPL_DIO_MOP_SHIFT                3
#define RPL_DIO_MOP_MASK                 0x38
#define RPL_DIO_PREFERENCE_MASK          0x07

#define UIP_IP_BUF       ((struct uip_ip_hdr *)&uip_buf[UIP_LLH_LEN])
#define UIP_ICMP_BUF     ((struct uip_icmp_hdr *)&uip_buf[uip_l2_l3_hdr_len])
#define UIP_ICMP_PAYLOAD ((unsigned char *)&uip_buf[uip_l2_l3_icmp_hdr_len])
/*---------------------------------------------------------------------------*/
static void dis_input(void);
static void dio_input(void);
static void dao_input(void);
static void dao_ack_input(void);

/* some debug callbacks useful when debugging RPL networks */
#ifdef RPL_DEBUG_DIO_INPUT   
void RPL_DEBUG_DIO_INPUT(uip_ipaddr_t *, rpl_dio_t *);
#endif

#ifdef RPL_DEBUG_DAO_OUTPUT
void RPL_DEBUG_DAO_OUTPUT(rpl_parent_t *);
#endif

static uint8_t dao_sequence = RPL_LOLLIPOP_INIT;

/*.........................................................................Amirreza....*/

//static int shomarande = 0;  //test : ok
//static int new_mobility = 1;
//static int child_count = 0;
//static int children[10] ; // 10 : max count of children
static int nbr_count = 10 ;  // number of neighbors (candidated parents)
static int critical_rss = 139;  //distance : 40 m
static int min_gap = -1 ;
static int max_gap = 12 ;
int rss_count = 3 ;   // number of last received rssi (of dio messages) 
static int nbr_ptr = 0 ;  //pointer to the current neighbor in nbrs array
static int nbr_rss_ptr[10] /*= {0,0,0,0,0,0,0,0,0,0}*/;    //pointer to the last rssi value of each neighbor   10= nbr count
static int nbr_ctr = 0 ;    //current number of neighbors (starts with 0)
static int nbrs[10] /*= {0,0,0,0,0,0,0,0,0,0}*/;   // array of neighbors (id)             10=nbr_count
static int candid_nbrs[10]; // 10: nbr_count
static int candid_nbr_cnt = 0 ;
static int dis_nbr[3]; //disconnected neighbors
//func() ;

static int nbr_link_quality[10][3] ;  //rssi container of neighbors                10=nbr_count  , 3= rss_count

void func(){   //initial values
	int ii = 0 ;
	for(ii=0 ; ii < nbr_count ; ii += 1){  //initial values
	   nbrs[ii] = (-1) ;
	   nbr_rss_ptr[ii] = 0 ;
	}
	int n =0 ;
	int m =0 ;
	for(n = 0 ; n< nbr_count ; n +=1){    //initial values
	    for(m=0 ; m<rss_count ; m +=1){
		nbr_link_quality[n][m] = 0 ;
	    }
	}
}

/*........................................................................Amirreza.....*/
extern rpl_of_t RPL_OF;

#if RPL_CONF_MULTICAST
static uip_mcast6_route_t *mcast_group;
#endif
/*---------------------------------------------------------------------------*/
/* Initialise RPL ICMPv6 message handlers */
UIP_ICMP6_HANDLER(dis_handler, ICMP6_RPL, RPL_CODE_DIS, dis_input);
UIP_ICMP6_HANDLER(dio_handler, ICMP6_RPL, RPL_CODE_DIO, dio_input);
UIP_ICMP6_HANDLER(dao_handler, ICMP6_RPL, RPL_CODE_DAO, dao_input);
UIP_ICMP6_HANDLER(dao_ack_handler, ICMP6_RPL, RPL_CODE_DAO_ACK, dao_ack_input);
/*---------------------------------------------------------------------------*/
static int
get_global_addr(uip_ipaddr_t *addr)
{
  int i;
  int state;

  for(i = 0; i < UIP_DS6_ADDR_NB; i++) {
    state = uip_ds6_if.addr_list[i].state;
    if(uip_ds6_if.addr_list[i].isused &&
       (state == ADDR_TENTATIVE || state == ADDR_PREFERRED)) {
      if(!uip_is_addr_link_local(&uip_ds6_if.addr_list[i].ipaddr)) {
        memcpy(addr, &uip_ds6_if.addr_list[i].ipaddr, sizeof(uip_ipaddr_t));
        return 1;
      }
    }
  }
  return 0;
}
/*---------------------------------------------------------------------------*/
static uint32_t
get32(uint8_t *buffer, int pos)
{
  return (uint32_t)buffer[pos] << 24 | (uint32_t)buffer[pos + 1] << 16 |
         (uint32_t)buffer[pos + 2] << 8 | buffer[pos + 3];
}
/*---------------------------------------------------------------------------*/
static void
set32(uint8_t *buffer, int pos, uint32_t value)
{
  buffer[pos++] = value >> 24;
  buffer[pos++] = (value >> 16) & 0xff;
  buffer[pos++] = (value >> 8) & 0xff;
  buffer[pos++] = value & 0xff;
}
/*---------------------------------------------------------------------------*/
static uint16_t
get16(uint8_t *buffer, int pos)
{
  return (uint16_t)buffer[pos] << 8 | buffer[pos + 1];
}
/*---------------------------------------------------------------------------*/
static void
set16(uint8_t *buffer, int pos, uint16_t value)
{
  buffer[pos++] = value >> 8;
  buffer[pos++] = value & 0xff;
}
/*---------------------------------------------------------------------------*/
static void
dis_input(void)
{
  rpl_instance_t *instance;
  rpl_instance_t *end;

  /* DAG Information Solicitation */
  PRINTF("RPL: Received a DIS from ");
  PRINT6ADDR(&UIP_IP_BUF->srcipaddr);
  PRINTF("\n");

  for(instance = &instance_table[0], end = instance + RPL_MAX_INSTANCES;
      instance < end; ++instance) {
    if(instance->used == 1) {
#if RPL_LEAF_ONLY
      if(!uip_is_addr_mcast(&UIP_IP_BUF->destipaddr)) {
	PRINTF("RPL: LEAF ONLY Multicast DIS will NOT reset DIO timer\n");
#else /* !RPL_LEAF_ONLY */
      if(uip_is_addr_mcast(&UIP_IP_BUF->destipaddr)) {
        PRINTF("RPL: Multicast DIS => reset DIO timer\n");
        rpl_reset_dio_timer(instance);
      } else {
#endif /* !RPL_LEAF_ONLY */
        PRINTF("RPL: Unicast DIS, reply to sender\n");
        dio_output(instance, &UIP_IP_BUF->srcipaddr);
      }
    }
  }
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
dis_output(uip_ipaddr_t *addr)
{
  unsigned char *buffer;
  uip_ipaddr_t tmpaddr;

  /*
   * DAG Information Solicitation  - 2 bytes reserved
   *      0                   1                   2
   *      0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3
   *     +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   *     |     Flags     |   Reserved    |   Option(s)...
   *     +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   */

  buffer = UIP_ICMP_PAYLOAD;
  buffer[0] = buffer[1] = 0;

  if(addr == NULL) {
    uip_create_linklocal_rplnodes_mcast(&tmpaddr);
    addr = &tmpaddr;
  }

  PRINTF("RPL: Sending a DIS to ");
  PRINT6ADDR(addr);
  PRINTF("\n");

  uip_icmp6_send(addr, ICMP6_RPL, RPL_CODE_DIS, 2);
}
/*---------------------------------------------------------------------------*/
static void
dio_input(void)
{
  unsigned char *buffer;
  uint8_t buffer_length;
  rpl_dio_t dio;
  uint8_t subopt_type;
  int i;
  int len;
  uip_ipaddr_t from;
  uip_ds6_nbr_t *nbr;

  memset(&dio, 0, sizeof(dio));

  /* Set default values in case the DIO configuration option is missing. */
  dio.dag_intdoubl = RPL_DIO_INTERVAL_DOUBLINGS;
  dio.dag_intmin = RPL_DIO_INTERVAL_MIN;
  dio.dag_redund = RPL_DIO_REDUNDANCY;
  dio.dag_min_hoprankinc = RPL_MIN_HOPRANKINC;
  dio.dag_max_rankinc = RPL_MAX_RANKINC;
  dio.ocp = RPL_OF.ocp;
  dio.default_lifetime = RPL_DEFAULT_LIFETIME;
  dio.lifetime_unit = RPL_DEFAULT_LIFETIME_UNIT;

  uip_ipaddr_copy(&from, &UIP_IP_BUF->srcipaddr);
  
  /* DAG Information Object */

/*...................................................................Amirreza.............................*/
  uint8_t rssi = packetbuf_attr(PACKETBUF_ATTR_RSSI) - 45 ;   //amirreza
//  linkaddr_t *rcvr = packetbuf_addr(PACKETBUF_ADDR_RECEIVER) ;
  //rpl_parent_t amirreza ;
/*...................................................................Amirreza.............................*/

  PRINTF("RPL: Received a DIO  with RSSI %u from ", rssi);  // amirreza
  PRINT6ADDR(&from);
  PRINTF("\n");
 
  //uint8_t rssi = cc2420_last_rssi - 45;
  if((nbr = uip_ds6_nbr_lookup(&from)) == NULL) {              //if the neighbor is new, add to nbr list
    if((nbr = uip_ds6_nbr_add(&from, (uip_lladdr_t *)
                              packetbuf_addr(PACKETBUF_ADDR_SENDER),
                              0, NBR_REACHABLE/*, rssi /* amirreza */)) != NULL) {
      /* set reachable timer */
      stimer_set(&nbr->reachable, UIP_ND6_REACHABLE_TIME / 1000);
      PRINTF("RPL: Neighbor added to neighbor cache ");
      PRINT6ADDR(&from);
      PRINTF(", ");
      PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      PRINTF("\n");
    } else {
      PRINTF("RPL: Out of memory, dropping DIO from ");
      PRINT6ADDR(&from);
      PRINTF(", ");
      PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      PRINTF("\n");
      return;
    }
  } else {
    PRINTF("RPL: Neighbor already in neighbor cache\n");
  }

  buffer_length = uip_len - uip_l3_icmp_hdr_len;

  /* Process the DIO base option. */
  i = 0;
  buffer = UIP_ICMP_PAYLOAD;

  dio.instance_id = buffer[i++];
  dio.version = buffer[i++];
  dio.rank = get16(buffer, i);
  i += 2;

  PRINTF("RPL: Incoming DIO (id, ver, rank) = (%u,%u,%u)\n",
         (unsigned)dio.instance_id,
         (unsigned)dio.version,
         (unsigned)dio.rank);

  dio.grounded = buffer[i] & RPL_DIO_GROUNDED;
  dio.mop = (buffer[i]& RPL_DIO_MOP_MASK) >> RPL_DIO_MOP_SHIFT;
  dio.preference = buffer[i++] & RPL_DIO_PREFERENCE_MASK;

  dio.dtsn = buffer[i++];
  /* two reserved bytes */
  i += 2;

  memcpy(&dio.dag_id, buffer + i, sizeof(dio.dag_id));
  i += sizeof(dio.dag_id);

  PRINTF("RPL: Incoming DIO (dag_id, pref) = (");
  PRINT6ADDR(&dio.dag_id);
  PRINTF(", %u)\n", dio.preference);

  /* Check if there are any DIO suboptions. */
  for(; i < buffer_length; i += len) {
    subopt_type = buffer[i];
    if(subopt_type == RPL_OPTION_PAD1) {
      len = 1;
    } else {
      /* Suboption with a two-byte header + payload */
      len = 2 + buffer[i + 1];
    }

    if(len + i > buffer_length) {
      PRINTF("RPL: Invalid DIO packet\n");
      RPL_STAT(rpl_stats.malformed_msgs++);
      return;
    }

    PRINTF("RPL: DIO option %u, length: %u\n", subopt_type, len - 2);

    switch(subopt_type) {      /* Suboption momkene dio option bashe ÖÖ amirreza vzn */
    case RPL_OPTION_DAG_METRIC_CONTAINER:
      if(len < 6) {
        PRINTF("RPL: Invalid DAG MC, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
        return;
      }
      dio.mc.type = buffer[i + 2];
      dio.mc.flags = buffer[i + 3] << 1;
      dio.mc.flags |= buffer[i + 4] >> 7;
      dio.mc.aggr = (buffer[i + 4] >> 4) & 0x3;
      dio.mc.prec = buffer[i + 4] & 0xf;
      dio.mc.length = buffer[i + 5];

      if(dio.mc.type == RPL_DAG_MC_NONE) {
        /* No metric container: do nothing */
      } else if(dio.mc.type == RPL_DAG_MC_ETX) {
        dio.mc.obj.etx = get16(buffer, i + 6);

        PRINTF("RPL: DAG MC: type %u, flags %u, aggr %u, prec %u, length %u, ETX %u\n",
	       (unsigned)dio.mc.type,
	       (unsigned)dio.mc.flags,
	       (unsigned)dio.mc.aggr,
	       (unsigned)dio.mc.prec,
	       (unsigned)dio.mc.length,
	       (unsigned)dio.mc.obj.etx);
      } else if(dio.mc.type == RPL_DAG_MC_ENERGY) {
        dio.mc.obj.energy.flags = buffer[i + 6];
        dio.mc.obj.energy.energy_est = buffer[i + 7];
      } else {
       PRINTF("RPL: Unhandled DAG MC type: %u\n", (unsigned)dio.mc.type);
       return;
      }
      break;
    case RPL_OPTION_ROUTE_INFO:
      if(len < 9) {
        PRINTF("RPL: Invalid destination prefix option, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
        return;
      }

      /* The flags field includes the preference value. */
      dio.destination_prefix.length = buffer[i + 2];
      dio.destination_prefix.flags = buffer[i + 3];
      dio.destination_prefix.lifetime = get32(buffer, i + 4);

      if(((dio.destination_prefix.length + 7) / 8) + 8 <= len &&
         dio.destination_prefix.length <= 128) {
        PRINTF("RPL: Copying destination prefix\n");
        memcpy(&dio.destination_prefix.prefix, &buffer[i + 8],
               (dio.destination_prefix.length + 7) / 8);
      } else {
        PRINTF("RPL: Invalid route info option, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
	return;
      }

      break;
    case RPL_OPTION_DAG_CONF:
      if(len != 16) {
        PRINTF("RPL: Invalid DAG configuration option, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
        return;
      }

      /* Path control field not yet implemented - at i + 2 */
      dio.dag_intdoubl = buffer[i + 3];
      dio.dag_intmin = buffer[i + 4];
      dio.dag_redund = buffer[i + 5];
      dio.dag_max_rankinc = get16(buffer, i + 6);
      dio.dag_min_hoprankinc = get16(buffer, i + 8);
      dio.ocp = get16(buffer, i + 10);
      /* buffer + 12 is reserved */
      dio.default_lifetime = buffer[i + 13];
      dio.lifetime_unit = get16(buffer, i + 14);
      PRINTF("RPL: DAG conf:dbl=%d, min=%d red=%d maxinc=%d mininc=%d ocp=%d d_l=%u l_u=%u\n",
             dio.dag_intdoubl, dio.dag_intmin, dio.dag_redund,
             dio.dag_max_rankinc, dio.dag_min_hoprankinc, dio.ocp,
             dio.default_lifetime, dio.lifetime_unit);
      break;
    case RPL_OPTION_PREFIX_INFO:
      if(len != 32) {
        PRINTF("RPL: Invalid DAG prefix info, len != 32\n");
	RPL_STAT(rpl_stats.malformed_msgs++);
        return;
      }
      dio.prefix_info.length = buffer[i + 2];
      dio.prefix_info.flags = buffer[i + 3];
      /* valid lifetime is ingnored for now - at i + 4 */
      /* preferred lifetime stored in lifetime */
      dio.prefix_info.lifetime = get32(buffer, i + 8);
      /* 32-bit reserved at i + 12 */
      PRINTF("RPL: Copying prefix information\n");
      memcpy(&dio.prefix_info.prefix, &buffer[i + 16], 16);
      break;
    default:
      PRINTF("RPL: Unsupported suboption type in DIO: %u\n",
	(unsigned)subopt_type);
    }
  }

#ifdef RPL_DEBUG_DIO_INPUT
  RPL_DEBUG_DIO_INPUT(&from, &dio);
#endif

//if(rssi > 175){dio.rank = 255;}  //Amirreza  : test

  rpl_process_dio(&from, &dio);

  uip_len = 0;

//.........................................................amirreza..........................................//

#if !DEBUG
//dag_connection experiment:
/*shomarande += 1;  //test : ok
if(shomarande == 5){
set_dag_con(0);
//printf("dag_connection is %u!\n",get_dag_con());     //commented
}*/
int my_state =0 ;  //if sendr is my parent : state =0    if sender is my child : state= 1 and if sender is my sibiling : state = 2
int destt = calculate_node_id(uip_ds6_nbr_lladdr_from_ipaddr(&from)) ;  //func return type : uip_lladdr_t *   :  destt : sender noede id
//printf("received DIO with rssi %u from %u \n", rssi, destt);                        //done in nbrs

rpl_instance_t *ins ;  //test : removable
ins = rpl_get_instance(dio.instance_id);   //test : removable
//printf("my parrent is %u\n", my_parent_id());                   //done in nbrs

//printf("dio min:%u, dio doubl:%u\n",ins->dio_intmin , ins->dio_intdoubl);   //test : ok
/*if(rssi<130){     //test : decreasing dio interval : works well!
printf("new intmin&doubl\n"); 
ins->dio_intmin = 10 ;
ins->dio_intcurrent = ins->dio_intmin;
ins->dio_intdoubl = 2 ;
}*/  
  
/*uint16_t res = 2 ;     //test : dio interval from algorithm by number of <received dio> from parent : ok 
int cnt = 0;
for(cnt = 0; cnt<dio_ctr_get()+1; cnt++){res *= 2;}*/

if(my_parent_id() == destt){
  //printf("sender is my parent!\n ");        //test : ok
  printf("dio wait time : %u\n",dio_wait_time_get() /*, res*//*,ins->dio_intcurrent*/);   //test : how much is dio interval  :ok
  dio_wait_time_set(0);
  if(dio_ctr_get() == 3){  //by 12_8 : after 9 dio, dio waiting time = 1048.576 sec = DIO_max => DIO RESET!  and by 12_2 : after 3 dio
    dio_ctr_set(1);
  }else{dio_ctr_set(dio_ctr_get()+1);}  //number of dio received from parent ++
  my_state = 0;                                          
}else{
   //my_state = 1;
   if(child_look(destt)){
     //printf("sender is my child!\n ");                //test : ok
     my_state = 1;    
   }else{/*printf("sender is my sibiling!\n ");*/  my_state = 2;}                              //test : ok
}

/*if(rssi < 150){  //blocklist test :ok
blocklist_add(destt);
}
if(rssi > 150){
blocklist_del(destt);
}*/

/*printf("blocklist is : [");                                             //bl : useless
int qq =0;
for(qq=0; qq<10; qq++){
   if(blocklist_get(qq) != 0){
       if(qq==9){printf(" %u ",blocklist_get(qq));}
       else{printf(" %u, ",blocklist_get(qq));}
   }
}
printf("]\n");*/                                                         

// int destt = calculate_node_id((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));   //ERROR  : incompatible format!
// filling the neighbor-rssi 2D list :
if(destt ==0){destt = 100 ;}   //contracted!
int nbr_exist = 0 ;
int cntr = 0 ; //counter
for(cntr = 0 ; cntr<nbr_count ; cntr +=1){  //check if this is a new neighbor or not?
   if(nbrs[cntr] == destt){
      nbr_exist = 1 ;     //this neighbor exists in nbrs
      nbr_ptr = cntr ;    // index of this neighbor in nbrs array
   }
}
if(!nbr_exist){  // if destt is a new neighbor
  if(nbr_ctr < nbr_count){
     nbrs[nbr_ctr] = destt;  // add to neighbors list
     nbr_ptr = nbr_ctr ;
     nbr_ctr += 1 ;  //number of neighbors ++
  }else {
     //printf("neighbors capacity is full!");                       //needed
     //break ;  
  }
}
int j = 0 ;
if (nbr_rss_ptr[nbr_ptr] == rss_count) {
  for(j = 0; j < (rss_count-1) ; j += 1){  //shift to left
     nbr_link_quality[nbr_ptr][j] = nbr_link_quality[nbr_ptr][j+1] ; 
  }
  nbr_link_quality[nbr_ptr][rss_count-1] = rssi ;  //add new rssi at right
} else {
     nbr_link_quality[nbr_ptr][nbr_rss_ptr[nbr_ptr]] = rssi ;
     nbr_rss_ptr[nbr_ptr] += 1 ;
}
//printing neighbor list with the last rssi of their dio :
int q = 0;
int w = 0 ; 
for(q=0 ; q< nbr_count ; q+= 1){
   if(nbrs[q] != 0){
      if(nbrs[q] == destt){printf("-->");}
      printf("nbr %u : ", nbrs[q]);
      for(w=0 ; w< rss_count ; w+= 1){
         if(w== rss_count-1){
           printf(" %u ", nbr_link_quality[q][w]);
           if(my_parent_id() == nbrs[q]){printf("  P");}
           printf("\n");
         }else {
           printf(" %u ,", nbr_link_quality[q][w]); 
         }
      }
   }
}

//Mobility detection :
int mobility = 0;
for(q=0; q<nbr_count ; q++){
  if((nbrs[q] != 0)&&(dis_nbr_lookup(nbrs[q]) == 0)){   //if q < nbr_ctr
    if(nbr_rss_ptr[q] > 1){  //if this neighbor had sent atleast 2 dio tu us!
      for(w=0; w < rss_count; w++){
         if(nbr_link_quality[q][nbr_rss_ptr[q]-2] != nbr_link_quality[q][nbr_rss_ptr[q]-1]){mobility = 1;} //if last 2 rssi of a neighbor aren't same, we have mobility here!
      }
    }
  }
}
int indx=0;
if(mobility == 1){  //reducing the dio interval : MM TRICKLE ACTIVATION
  //printf("mobility!\n");  //TEST : OK
  ins->dio_intmin = 10 ;
  ins->dio_intdoubl = 2 ;  //new dio interval : DIO_min: 1.024  to   DIO_max: 4.096 (second)
  if(new_mobility_get()){  //new_mobility
    ins->dio_intcurrent = ins->dio_intmin;
    //new_mobility = 0 ; 
    new_mobility_set(0);
    set_instance_id(dio.instance_id);
    //set_instance(&ins);
    //printf("mm"); //test : ok
    if(my_state == 0){
      indx = index_of_nbrs(destt) ;
      if(nbr_rss_ptr[indx]>1){ 
        if(nbr_link_quality[indx][nbr_rss_ptr[indx]-2] != nbr_link_quality[indx][nbr_rss_ptr[indx]-1]){
           dio_ctr_set(1);
        }
      }
    }
    //printf("new mobility\n");   //test : ok
  }
//new dio interval : DIO_min: 1.024  to   DIO_max: 4.096 
}else{  //BACK TO BASIC TRICKLE TIMER
  //printf("static\n");       //test : ok
  ins->dio_intmin = 12 ;
  ins->dio_intdoubl = 2 ;
  //new_mobility = 1;
  new_mobility_set(1);
  dio_conf_flag_set(1);
//new dio interval : DIO_min: 4.096  to   DIO_max: 16.384 (second)
}

// finding candidate neighbors
int y = 0 ;
int permission = 1;
int delta = 0 ;
for(q=0; q<nbr_count ; q++){candid_nbrs[q]=0;}

for(q=0 ; q < nbr_count ; q++){
   permission = 1 ;
   delta = 0 ;
   for(w=2; w < rss_count ; w++){
       delta = nbr_link_quality[q][w] - nbr_link_quality[q][w-1]; 
       if((delta < 0) || (nbr_link_quality[q][rss_count-1] == 0)){/*printf("%u w\n", a2);*/ permission = 0 ;}  // 3 rssi value must be filled ! and shoudnt be decreasing!
   }
   if(permission){  //rssi values are not decreasing & we have 3 rssi values 
      if(!child_look(nbrs[q])){  //if the neighbor isn't in children list 
        candid_nbrs[y] = nbrs[q];   // Updating the candidate neighbors list :
        //arr[y] = nbrs[a1] ;
        //printf("*\n");
        y++;
      } /*else{if(dis_nbrs_look(nbrs[q])){candid_nbrs[y]=nbrs[q]; y++;}}*/ //if the node WAS one of our children and we had disconnected from thad before :FALSE
   }
}
candid_nbr_cnt = y ; //number of candidate neighbors

//printf("best pp  : %u\n", my_best_parent());  //works well !
//printf("candids : %u , %u , %u , %u \n" , candid_nbrs[0], candid_nbrs[1], candid_nbrs[2], candid_nbrs[3]);  //works well!
//printf("children : %u , %u , %u , %u \n" , children_get(0), children_get(1), children_get(2), children_get(3));  //works well!
//###################################### DAO experiment  (dao test : ok)
/*if((rssi > 175) && (destt == 4)){
	rpl_instance_t *ins ;
	dao_output(parent_of_id(destt), ins->default_lifetime);
        cur_parent_set(destt);
        neww_parent(destt);
        //printf("my parent changed to %u \n", my_parent_id());
        parent_modification_permit_set(0) ;
        //printf("snd dao to %u ! \n", id_of_parent(parent_of_id(destt)));
}*/
//########################################

//removing from the block list :    works well!
if(!destt){  
  if(blocklist_look(destt)){ //if sender is in our blocklist
    delta =0;
    permission=1;
    for(q=2; q<rss_count; q++){
      delta = nbr_link_quality[index_of_nbrs(destt)][q] - nbr_link_quality[index_of_nbrs(destt)][q-1];
      if(delta <0){permission = 0;}
    }
    if(permission){ //sender is not getting far (its static or getting closer to us)
      blocklist_del(destt); //remove neighbor from blocklist
    }
  }
}
//if((rssi<130)&&(my_state == 0)){set_dag_con(0); printf("diss\n");}  //Amirreza test : Works well!
//if((rssi<130)&&(my_state == 0)){printf("D\n"); set_dag_con(0);}  //test : works well!
//########################################################################### main part 

int best_candid=0 ;
best_candid = my_best_parent();
//if(nbr_link_quality[index_of_nbrs(5)][rss_count-1] != 0){best_candid = 5;}   //Amirreza test   :task 8 works well  ok
//best_candid= 5 ; //test  : task5 works well ok
//rpl_instance_t *ins ;

if(get_dag_con()==0){  // if we are disconnected before
  if((best_candid != 0)&&(best_candid == destt)){  // if there is any candidate parent and candidate paret is the DIO sender
    set_dag_con(1);
    dao_output(parent_of_id(best_candid), ins->default_lifetime); //send dao to best candidate parent 
    cur_parent_set(best_candid);  //and reset ur parent id
    neww_parent(best_candid);
    printf("P -> %u\n", my_parent_id());  //parent chaged to x //works well
    parent_modification_permit_set(0) ;  //avoiding parent selection by dag rank !  because the node is mobile and now nodes rank is set by rssi!
    dio_wait_time_set(0);
    dio_ctr_set(1);  //first dio from new parent
  }
}

//main part : //if we are getting far from each other :
if(get_dag_con()){
	delta=0;
	permission = 1;
	if((nbr_exist)&&(nbr_link_quality[index_of_nbrs(destt)][rss_count-1] != 0)){  //if this node is not new neighbor and we got atleast 3 dio of that.
	  if(rssi < critical_rss){  //if our distance is exceeding to the critical zone
	    for(q=1; q<rss_count ; q++){
	       delta = nbr_link_quality[index_of_nbrs(destt)][q] - nbr_link_quality[index_of_nbrs(destt)][q-1];
	       if(delta > min_gap){permission = 0;}
	    }
	    if(permission){ //we got 3 decreasing dio from this neighbor: so we have to disconnect! 
	      if(my_state == 0){ //if sender is my parent 
                dis_nbr_add(destt);
		if(best_candid != 0){  //if there is a candid parent
		  dao_output(parent_of_id(best_candid), ins->default_lifetime); //send dao to best candidate parent 
		  cur_parent_set(best_candid);  //and reset ur parent id
		  neww_parent(best_candid);
		  printf("P -> %u\n", my_parent_id());   //parent chaged to x //works well!
		  parent_modification_permit_set(0) ;  //avoiding parent selection by dag rank !  because the node is mobile and now nodes rank is set by rssi!
                  dio_wait_time_set(0);
	          //dio_ctr_set(0);
		}else{ //if there is no any candid parent  
		  set_dag_con(0);  //just disconnect from dag and avoid sending dio till reconnetion!
		  dio_ctr_set(0);
                  printf("dis\n");
		}
	      }
	      if(my_state != 0){  // if sender is my child or my sibiling
		blocklist_add(destt); //adding this child or sibiling to my blocklist
                dis_nbr_add(destt);
		if(my_state == 1){child_del(destt); /*printf("d%u\n",destt);*/} // if sender was my child, delete it from children list
	      }
	    }
	  }
	}
}
//if(destt ==2){if(rssi==141){parent_modification_permit_set(0); printf("diz");}}  //disables the RPL Default DIO waiting timer : scenario trickle12_8
//################################################################################ main part
#endif 
//.............................................................amirreza.......................................................//

}
/*---------------------------------------------------------------------------*/
void
dio_output(rpl_instance_t *instance, uip_ipaddr_t *uc_addr)
{
if(get_dag_con()){   //Amirreza    each node can send dio msg just if its connected to dag !
  unsigned char *buffer;
  int pos;
  rpl_dag_t *dag = instance->current_dag;
#if !RPL_LEAF_ONLY
  uip_ipaddr_t addr;
#endif /* !RPL_LEAF_ONLY */

#if RPL_LEAF_ONLY
  /* In leaf mode, we only send DIO messages as unicasts in response to
     unicast DIS messages. */
  if(uc_addr == NULL) {
    PRINTF("RPL: LEAF ONLY have multicast addr: skip dio_output\n");
    return;
  }
#endif /* RPL_LEAF_ONLY */

  /* DAG Information Object */
  pos = 0;

  buffer = UIP_ICMP_PAYLOAD;
  buffer[pos++] = instance->instance_id;
  buffer[pos++] = dag->version;

#if RPL_LEAF_ONLY
  PRINTF("RPL: LEAF ONLY DIO rank set to INFINITE_RANK\n");
  set16(buffer, pos, INFINITE_RANK);
#else /* RPL_LEAF_ONLY */
  set16(buffer, pos, dag->rank);
#endif /* RPL_LEAF_ONLY */
  pos += 2;

  buffer[pos] = 0;
  if(dag->grounded) {
    buffer[pos] |= RPL_DIO_GROUNDED;
  }

  buffer[pos] |= instance->mop << RPL_DIO_MOP_SHIFT;
  buffer[pos] |= dag->preference & RPL_DIO_PREFERENCE_MASK;
  pos++;

  buffer[pos++] = instance->dtsn_out;

  if(uc_addr == NULL) {
    /* Request new DAO to refresh route. We do not do this for unicast DIO
     * in order to avoid DAO messages after a DIS-DIO update,
     * or upon unicast DIO probing. */
    RPL_LOLLIPOP_INCREMENT(instance->dtsn_out);
  }

  /* reserved 2 bytes */
  buffer[pos++] = 0; /* flags */
  buffer[pos++] = 0; /* reserved */

  memcpy(buffer + pos, &dag->dag_id, sizeof(dag->dag_id));
  pos += 16;

#if !RPL_LEAF_ONLY
  if(instance->mc.type != RPL_DAG_MC_NONE) {
    instance->of->update_metric_container(instance);

    buffer[pos++] = RPL_OPTION_DAG_METRIC_CONTAINER;
    buffer[pos++] = 6;
    buffer[pos++] = instance->mc.type;
    buffer[pos++] = instance->mc.flags >> 1;
    buffer[pos] = (instance->mc.flags & 1) << 7;
    buffer[pos++] |= (instance->mc.aggr << 4) | instance->mc.prec;
    if(instance->mc.type == RPL_DAG_MC_ETX) {
      buffer[pos++] = 2;
      set16(buffer, pos, instance->mc.obj.etx);
      pos += 2;
    } else if(instance->mc.type == RPL_DAG_MC_ENERGY) {
      buffer[pos++] = 2;
      buffer[pos++] = instance->mc.obj.energy.flags;
      buffer[pos++] = instance->mc.obj.energy.energy_est;
    } else {
      PRINTF("RPL: Unable to send DIO because of unhandled DAG MC type %u\n",
	(unsigned)instance->mc.type);
      return;
    }
  }
#endif /* !RPL_LEAF_ONLY */

  /* Always add a DAG configuration option. */
  buffer[pos++] = RPL_OPTION_DAG_CONF;
  buffer[pos++] = 14;
  buffer[pos++] = 0; /* No Auth, PCS = 0 */
  buffer[pos++] = instance->dio_intdoubl;
  buffer[pos++] = instance->dio_intmin;
  buffer[pos++] = instance->dio_redundancy;
  set16(buffer, pos, instance->max_rankinc);
  pos += 2;
  set16(buffer, pos, instance->min_hoprankinc);
  pos += 2;
  /* OCP is in the DAG_CONF option */
  set16(buffer, pos, instance->of->ocp);
  pos += 2;
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = instance->default_lifetime;
  set16(buffer, pos, instance->lifetime_unit);
  pos += 2;

  /* Check if we have a prefix to send also. */
  if(dag->prefix_info.length > 0) {
    buffer[pos++] = RPL_OPTION_PREFIX_INFO;
    buffer[pos++] = 30; /* always 30 bytes + 2 long */
    buffer[pos++] = dag->prefix_info.length;
    buffer[pos++] = dag->prefix_info.flags;
    set32(buffer, pos, dag->prefix_info.lifetime);
    pos += 4;
    set32(buffer, pos, dag->prefix_info.lifetime);
    pos += 4;
    memset(&buffer[pos], 0, 4);
    pos += 4;
    memcpy(&buffer[pos], &dag->prefix_info.prefix, 16);
    pos += 16;
    PRINTF("RPL: Sending prefix info in DIO for ");
    PRINT6ADDR(&dag->prefix_info.prefix);
    PRINTF("\n");
  } else {
    PRINTF("RPL: No prefix to announce (len %d)\n",
           dag->prefix_info.length);
  }

#if RPL_LEAF_ONLY
#if (DEBUG) & DEBUG_PRINT
  if(uc_addr == NULL) {
    PRINTF("RPL: LEAF ONLY sending unicast-DIO from multicast-DIO\n");
  }
#endif /* DEBUG_PRINT */
  PRINTF("RPL: Sending unicast-DIO with rank %u to ",
      (unsigned)dag->rank);
  PRINT6ADDR(uc_addr);
  PRINTF("\n");
  uip_icmp6_send(uc_addr, ICMP6_RPL, RPL_CODE_DIO, pos);
#else /* RPL_LEAF_ONLY */
  /* Unicast requests get unicast replies! */
  if(uc_addr == NULL) {
    PRINTF("RPL: Sending a multicast-DIO with rank %u\n",
        (unsigned)instance->current_dag->rank);
    uip_create_linklocal_rplnodes_mcast(&addr);
    uip_icmp6_send(&addr, ICMP6_RPL, RPL_CODE_DIO, pos);
  } else {
    PRINTF("RPL: Sending unicast-DIO with rank %u to ",
        (unsigned)instance->current_dag->rank);
    PRINT6ADDR(uc_addr);
    PRINTF("\n");
    uip_icmp6_send(uc_addr, ICMP6_RPL, RPL_CODE_DIO, pos);
  }
#endif /* RPL_LEAF_ONLY */
}else{  //Amirreza
#if !DEBUG   //Amirreza
printf("dio banned!\n");}  //Amirreza
#endif    //Amirreza
}
/*---------------------------------------------------------------------------*/
static void
dao_input(void)
{
  uip_ipaddr_t dao_sender_addr;
  rpl_dag_t *dag;
  rpl_instance_t *instance;
  unsigned char *buffer;
  uint16_t sequence;
  uint8_t instance_id;
  uint8_t lifetime;
  uint8_t prefixlen;
  uint8_t flags;
  uint8_t subopt_type;
  /*
  uint8_t pathcontrol;
  uint8_t pathsequence;
  */
  uip_ipaddr_t prefix;
  uip_ds6_route_t *rep;
  uint8_t buffer_length;
  int pos;
  int len;
  int i;
  int learned_from;
  rpl_parent_t *parent;
  uip_ds6_nbr_t *nbr;

  prefixlen = 0;
  parent = NULL;

  uip_ipaddr_copy(&dao_sender_addr, &UIP_IP_BUF->srcipaddr);

  /* Destination Advertisement Object */
  PRINTF("RPL: Received a DAO from ");
  PRINT6ADDR(&dao_sender_addr);
  PRINTF("\n");

/*....................................................................Amirreza...............*/
int new_child = calculate_node_id(uip_ds6_nbr_lladdr_from_ipaddr(&dao_sender_addr)) ;
if((!child_look(new_child))&&(new_child != 0)){
child_add(new_child);
//children[child_count] = new_child ;
//child_count ++;
}
/*....................................................................Amirreza...............*/

  buffer = UIP_ICMP_PAYLOAD;
  buffer_length = uip_len - uip_l3_icmp_hdr_len;

  pos = 0;
  instance_id = buffer[pos++];

  instance = rpl_get_instance(instance_id);
  if(instance == NULL) {
    PRINTF("RPL: Ignoring a DAO for an unknown RPL instance(%u)\n",
           instance_id);
    return;
  }

  lifetime = instance->default_lifetime;

  flags = buffer[pos++];
  /* reserved */
  pos++;
  sequence = buffer[pos++];

  dag = instance->current_dag;
  /* Is the DAG ID present? */
  if(flags & RPL_DAO_D_FLAG) {
    if(memcmp(&dag->dag_id, &buffer[pos], sizeof(dag->dag_id))) {
      PRINTF("RPL: Ignoring a DAO for a DAG different from ours\n");
      return;
    }
    pos += 16;
  }

  learned_from = uip_is_addr_mcast(&dao_sender_addr) ?
                 RPL_ROUTE_FROM_MULTICAST_DAO : RPL_ROUTE_FROM_UNICAST_DAO;

  PRINTF("RPL: DAO from %s\n",
         learned_from == RPL_ROUTE_FROM_UNICAST_DAO? "unicast": "multicast");
  if(learned_from == RPL_ROUTE_FROM_UNICAST_DAO) {
    /* Check whether this is a DAO forwarding loop. */
    parent = rpl_find_parent(dag, &dao_sender_addr);
    /* check if this is a new DAO registration with an "illegal" rank */
    /* if we already route to this node it is likely */
    if(parent != NULL &&
       DAG_RANK(parent->rank, instance) < DAG_RANK(dag->rank, instance)) {
      PRINTF("RPL: Loop detected when receiving a unicast DAO from a node with a lower rank! (%u < %u)\n",
          DAG_RANK(parent->rank, instance), DAG_RANK(dag->rank, instance));
      parent->rank = INFINITE_RANK;
      parent->flags |= RPL_PARENT_FLAG_UPDATED;
      return;
    }

    /* If we get the DAO from our parent, we also have a loop. */
    if(parent != NULL && parent == dag->preferred_parent) {
      PRINTF("RPL: Loop detected when receiving a unicast DAO from our parent\n");
      parent->rank = INFINITE_RANK;
      parent->flags |= RPL_PARENT_FLAG_UPDATED;
      return;
    }
  }

  /* Check if there are any RPL options present. */
  for(i = pos; i < buffer_length; i += len) {
    subopt_type = buffer[i];
    if(subopt_type == RPL_OPTION_PAD1) {
      len = 1;
    } else {
      /* The option consists of a two-byte header and a payload. */
      len = 2 + buffer[i + 1];
    }

    switch(subopt_type) {
    case RPL_OPTION_TARGET:
      /* Handle the target option. */
      prefixlen = buffer[i + 3];
      memset(&prefix, 0, sizeof(prefix));
      memcpy(&prefix, buffer + i + 4, (prefixlen + 7) / CHAR_BIT);
      break;
    case RPL_OPTION_TRANSIT:
      /* The path sequence and control are ignored. */
      /*      pathcontrol = buffer[i + 3];
              pathsequence = buffer[i + 4];*/
      lifetime = buffer[i + 5];
      /* The parent address is also ignored. */
      break;
    }
  }

  PRINTF("RPL: DAO lifetime: %u, prefix length: %u prefix: ",
          (unsigned)lifetime, (unsigned)prefixlen);
  PRINT6ADDR(&prefix);
  PRINTF("\n");

#if RPL_CONF_MULTICAST
  if(uip_is_addr_mcast_global(&prefix)) {
    mcast_group = uip_mcast6_route_add(&prefix);
    if(mcast_group) {
      mcast_group->dag = dag;
      mcast_group->lifetime = RPL_LIFETIME(instance, lifetime);
    }
    goto fwd_dao;
  }
#endif

  rep = uip_ds6_route_lookup(&prefix);

  if(lifetime == RPL_ZERO_LIFETIME) {
    PRINTF("RPL: No-Path DAO received\n");
    /* No-Path DAO received; invoke the route purging routine. */
    if(rep != NULL &&
       rep->state.nopath_received == 0 &&
       rep->length == prefixlen &&
       uip_ds6_route_nexthop(rep) != NULL &&
       uip_ipaddr_cmp(uip_ds6_route_nexthop(rep), &dao_sender_addr)) {
      PRINTF("RPL: Setting expiration timer for prefix ");
      PRINT6ADDR(&prefix);
      PRINTF("\n");
      rep->state.nopath_received = 1;
      rep->state.lifetime = DAO_EXPIRATION_TIMEOUT;

      /* We forward the incoming no-path DAO to our parent, if we have
         one. */
      if(dag->preferred_parent != NULL &&
         rpl_get_parent_ipaddr(dag->preferred_parent) != NULL) {
        PRINTF("RPL: Forwarding no-path DAO to parent ");
        PRINT6ADDR(rpl_get_parent_ipaddr(dag->preferred_parent));
        PRINTF("\n");
        uip_icmp6_send(rpl_get_parent_ipaddr(dag->preferred_parent),
                       ICMP6_RPL, RPL_CODE_DAO, buffer_length);
      }
      if(flags & RPL_DAO_K_FLAG) {
        dao_ack_output(instance, &dao_sender_addr, sequence);
      }
    }
    return;
  }

  PRINTF("RPL: adding DAO route\n");
  //uint8_t rssi = cc2420_last_rssi - 45;
  uint8_t rssi = packetbuf_attr(PACKETBUF_ATTR_RSSI) - 45 ; //amirreza
  if((nbr = uip_ds6_nbr_lookup(&dao_sender_addr)) == NULL) {
    if((nbr = uip_ds6_nbr_add(&dao_sender_addr,
                              (uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER),
                              0, NBR_REACHABLE/*, rssi /* amirreza */)) != NULL) {
      /* set reachable timer */
      stimer_set(&nbr->reachable, UIP_ND6_REACHABLE_TIME / 1000);
      PRINTF("RPL: Neighbor added to neighbor cache ");
      PRINT6ADDR(&dao_sender_addr);
      PRINTF(", ");
      PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      PRINTF("\n");
    } else {
      PRINTF("RPL: Out of Memory, dropping DAO from ");
      PRINT6ADDR(&dao_sender_addr);
      PRINTF(", ");
      PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      PRINTF("\n");
      return;
    }
  } else {
    PRINTF("RPL: Neighbor already in neighbor cache\n");
  }

  rpl_lock_parent(parent);

  rep = rpl_add_route(dag, &prefix, prefixlen, &dao_sender_addr);
  if(rep == NULL) {
    RPL_STAT(rpl_stats.mem_overflows++);
    PRINTF("RPL: Could not add a route after receiving a DAO\n");
    return;
  }

  rep->state.lifetime = RPL_LIFETIME(instance, lifetime);
  rep->state.learned_from = learned_from;
  rep->state.nopath_received = 0;

#if RPL_CONF_MULTICAST
fwd_dao:
#endif

  if(learned_from == RPL_ROUTE_FROM_UNICAST_DAO) {
    if(dag->preferred_parent != NULL &&
       rpl_get_parent_ipaddr(dag->preferred_parent) != NULL) {
      PRINTF("RPL: Forwarding DAO to parent ");
      PRINT6ADDR(rpl_get_parent_ipaddr(dag->preferred_parent));
      PRINTF("\n");
      uip_icmp6_send(rpl_get_parent_ipaddr(dag->preferred_parent),
                     ICMP6_RPL, RPL_CODE_DAO, buffer_length);
    }
    if(flags & RPL_DAO_K_FLAG) {
      dao_ack_output(instance, &dao_sender_addr, sequence);
    }
  }
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
dao_output(rpl_parent_t *parent, uint8_t lifetime)
{
  /* Destination Advertisement Object */
  uip_ipaddr_t prefix;

  if(get_global_addr(&prefix) == 0) {
    PRINTF("RPL: No global address set for this node - suppressing DAO\n");
    return;
  }

  /* Sending a DAO with own prefix as target */
  dao_output_target(parent, &prefix, lifetime);
}
/*---------------------------------------------------------------------------*/
void
dao_output_target(rpl_parent_t *parent, uip_ipaddr_t *prefix, uint8_t lifetime)
{
  rpl_dag_t *dag;
  rpl_instance_t *instance;
  unsigned char *buffer;
  uint8_t prefixlen;
  int pos;

  /* Destination Advertisement Object */

  /* If we are in feather mode, we should not send any DAOs */
  if(rpl_get_mode() == RPL_MODE_FEATHER) {
    return;
  }

  if(parent == NULL) {
    PRINTF("RPL dao_output_target error parent NULL\n");
    return;
  }

  dag = parent->dag;
  if(dag == NULL) {
    PRINTF("RPL dao_output_target error dag NULL\n");
    return;
  }

  instance = dag->instance;

  if(instance == NULL) {
    PRINTF("RPL dao_output_target error instance NULL\n");
    return;
  }
  if(prefix == NULL) {
    PRINTF("RPL dao_output_target error prefix NULL\n");
    return;
  }
#ifdef RPL_DEBUG_DAO_OUTPUT
  RPL_DEBUG_DAO_OUTPUT(parent);
#endif

  buffer = UIP_ICMP_PAYLOAD;

  RPL_LOLLIPOP_INCREMENT(dao_sequence);
  pos = 0;

  buffer[pos++] = instance->instance_id;
  buffer[pos] = 0;
#if RPL_DAO_SPECIFY_DAG
  buffer[pos] |= RPL_DAO_D_FLAG;
#endif /* RPL_DAO_SPECIFY_DAG */
#if RPL_CONF_DAO_ACK
  buffer[pos] |= RPL_DAO_K_FLAG;
#endif /* RPL_CONF_DAO_ACK */
  ++pos;
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = dao_sequence;
#if RPL_DAO_SPECIFY_DAG
  memcpy(buffer + pos, &dag->dag_id, sizeof(dag->dag_id));
  pos+=sizeof(dag->dag_id);
#endif /* RPL_DAO_SPECIFY_DAG */

  /* create target subopt */
  prefixlen = sizeof(*prefix) * CHAR_BIT;
  buffer[pos++] = RPL_OPTION_TARGET;
  buffer[pos++] = 2 + ((prefixlen + 7) / CHAR_BIT);
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = prefixlen;
  memcpy(buffer + pos, prefix, (prefixlen + 7) / CHAR_BIT);
  pos += ((prefixlen + 7) / CHAR_BIT);

  /* Create a transit information sub-option. */
  buffer[pos++] = RPL_OPTION_TRANSIT;
  buffer[pos++] = 4;
  buffer[pos++] = 0; /* flags - ignored */
  buffer[pos++] = 0; /* path control - ignored */
  buffer[pos++] = 0; /* path seq - ignored */
  buffer[pos++] = lifetime;

  PRINTF("RPL: Sending DAO with prefix ");
  PRINT6ADDR(prefix);
  PRINTF(" to ");
  PRINT6ADDR(rpl_get_parent_ipaddr(parent));
  PRINTF("\n");

  if(rpl_get_parent_ipaddr(parent) != NULL) {
    uip_icmp6_send(rpl_get_parent_ipaddr(parent), ICMP6_RPL, RPL_CODE_DAO, pos);
  }
}
/*---------------------------------------------------------------------------*/
static void
dao_ack_input(void)
{
#if DEBUG
  unsigned char *buffer;
  uint8_t buffer_length;
  uint8_t instance_id;
  uint8_t sequence;
  uint8_t status;

  buffer = UIP_ICMP_PAYLOAD;
  buffer_length = uip_len - uip_l3_icmp_hdr_len;

  instance_id = buffer[0];
  sequence = buffer[2];
  status = buffer[3];

  PRINTF("RPL: Received a DAO ACK with sequence number %d and status %d from ",
    sequence, status);
  PRINT6ADDR(&UIP_IP_BUF->srcipaddr);
  PRINTF("\n");
#endif /* DEBUG */
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
dao_ack_output(rpl_instance_t *instance, uip_ipaddr_t *dest, uint8_t sequence)
{
  unsigned char *buffer;

  PRINTF("RPL: Sending a DAO ACK with sequence number %d to ", sequence);
  PRINT6ADDR(dest);
  PRINTF("\n");

  buffer = UIP_ICMP_PAYLOAD;

  buffer[0] = instance->instance_id;
  buffer[1] = 0;
  buffer[2] = sequence;
  buffer[3] = 0;

  uip_icmp6_send(dest, ICMP6_RPL, RPL_CODE_DAO_ACK, 4);
}
/*---------------------------------------------------------------------------*/
void
rpl_icmp6_register_handlers()
{
  uip_icmp6_register_input_handler(&dis_handler);
  uip_icmp6_register_input_handler(&dio_handler);
  uip_icmp6_register_input_handler(&dao_handler);
  uip_icmp6_register_input_handler(&dao_ack_handler);
}
/*---------------------------------------------------------------------------*/
/*.....................................................................................Amirreza.....*/
/*int best_par(){
  int output = 0;
  int i = 0 ;
  int x=0;
  for(i = 0 ; i < nbr_count; i++){
     if(candid_nbrs[i] != 0) {
        x++ ;
     }
  }
  if(x == 0){ 
     //printf("0*\n");
     return 0 ;
  }  // there is not any candidate parent!
  //Else :
  // first consider constant rssi (static nodes):
  int rss_val = 0 ;
  int delta = 0 ;
  int permission = 1;
  int j = 0 ;
  for(i=0 ; i<nbr_count ; i++){
     delta = 0 ;
     permission = 1 ;
     for(j=1 ; j < rss_count ; j++){
        //delta = nbr_link_quality[i][j] - delta ;
        //if(j == 0){delta = nbr_link_quality[i][j];}
        delta = nbr_link_quality[i][j] - nbr_link_quality[i][j-1]; 
        if(delta>0){
          permission = 0 ; //}
        }    
     }
     if(permission){
       if(candid_lookup(nbrs[i])){
         if(rss_val < nbr_link_quality[i][rss_count-1]){  // best static neighbor : having greater rssi
           rss_val = nbr_link_quality[i][rss_count-1] ; 
           output = nbrs[i] ; 
         }
       }
     }
  }
  if(output > 0){
     //printf("1*\n");
     return output;
  }
  if(!output){  // if there is no any static neighbor
    rss_val = 1000;
  // second look for neighbor which we are getting close to that and one of us is static!
    for(i=0 ; i< nbr_count ; i++){
       delta = 0 ;
       permission = 1 ;
       for(j=1; j< rss_count ; j++){
          //delta = nbr_link_quality[i][j] - delta ;
          //if(j == 0){delta = nbr_link_quality[i][j];}
          delta = nbr_link_quality[i][j] - nbr_link_quality[i][j-1]; 
          if(delta > max_gap){   //if((j>0)&&((delta<min_gap)||(delta>max_gap)))
             permission = 0 ;//}
          }
       }
       if(permission){
             // printf("#\n");
         if(candid_lookup(nbrs[i])){  //look for best oncoming neighbor with less rssi (more durable connection) 
            //  printf("##\n");
           if(nbr_link_quality[i][rss_count-1] < rss_val){
            //  printf("###");
             rss_val = nbr_link_quality[i][rss_count-1] ; 
             output = nbrs[i];
           }
         }
       }
    }
  }
  if(output > 0){
    //printf("2*\n"); 
    return output;}
  //###################################
   if(!output){   //there is no any oncoming candidate neighbor having rssi between min_gap and max_gap !   if output is still 0
  // third we have to look for nodes with one decreasing rssi and then turning to constant rssi or increasing rssi's:
    rss_val = 0;
    for(i=0; i< nbr_count ; i++){
       delta = 0 ;
       permission = 1 ;
       for(j=2 ; j < rss_count ; j++){  //if we have 3 rssi of each nbr, considers last two rssi if those are constant or increasing that would be ok!
          delta =  nbr_link_quality[i][j] - nbr_link_quality[i][j-1];
          if(delta<0) {permission = 0 ;}
       }
       if(permission){
         if(candid_lookup(nbrs[i])){
           if(nbr_link_quality[i][rss_count-1] > rss_val){  // best neighbor in this section : whom have greater rss value 
             rss_val = nbr_link_quality[i][rss_count-1] ;
             output = nbrs[i] ;
           }
         }
       }
    } 
  }
  if(output >0){
  //printf("3*\n");
  return output;}
  //####################################
  if(!output){   //there is no any oncoming candidate neighbor having rssi between min_gap and max_gap !   if output is still 0
  // there are just neighbors whom we are both getting close to each other : so rssi is increasing with big steps
    rss_val = 1000;
    for(i=0; i< nbr_count ; i++){
       delta = 0 ;
       permission = 1 ;
       for(j=1 ; j < rss_count ; j++){
          delta =  nbr_link_quality[i][j] - nbr_link_quality[i][j-1];
          if(delta<max_gap) {permission = 0 ;}
       }
       if(permission){
         if(candid_lookup(nbrs[i])){
           if(nbr_link_quality[i][rss_count-1] < rss_val){  // best oncoming neighbor : whom have less rss value due to more durable connection!
             rss_val = nbr_link_quality[i][rss_count-1] ;
             output = nbrs[i] ;
           }
         }
       }
    } 
  
  }

 // printf("*****\n");
  return output ;
} */

int my_best_parent(){
//#if !DEBUG
  if(candid_nbr_cnt == 0){return 0;}  //there is no any candidate neighbor
  int output1 = 0; 
  int output2 = 0;
  int output3 = 0;
  int output4 = 0;
  int rss_val1 = 0;
  int rss_val3 = 0;
  int rss_val2 = 999;
  int rss_val4 = 999;
  int i = 0 ;
  int j = 0 ;
  int delta = 0 ;
  int permission1 = 1 ;   // constant rssi (3 rssi)
  int permission2 = 1 ;   // increasing rssi with small steps
  int permission3 = 1 ;   // one decrease and then constant or increase
  int permission4 = 1 ;   // increasnig rssi with big steps
  int nbr_index = 0 ;
  for(i=0; i<candid_nbr_cnt ; i++){
     nbr_index = index_of_nbrs(candid_nbrs[i]);
     //printf("ca%u\n",candid_nbrs[i]);
     delta = 0 ;
     //permission1 =1 ;
     //permission2 =1 ;
     //permission3 =1 ;
     //permission4 =1 ;
     for(j=1; j<rss_count ; j++){
        delta = nbr_link_quality[nbr_index][j] - nbr_link_quality[nbr_index][j-1];
        if(delta != 0){permission1 = 0 ;}
        if((delta <= 0) || (delta > max_gap)){permission2 = 0 ;}
        if((j>1)&&(delta < 0)){permission3 = 0 ;}
        if(delta < max_gap){permission4 = 0 ;}
     }
     if(permission1){ //printf("1\n");
       if(rss_val1 <= nbr_link_quality[nbr_index][rss_count-1]){   // best static neighbor : having greater rssi
         rss_val1 = nbr_link_quality[nbr_index][rss_count-1] ; 
         output1 = candid_nbrs[i] ; //printf("%u\n", output1);
       }
       permission2 = 0 ;
       permission3 = 0 ;
       permission4 = 0 ;
     }
     if(permission2){ //printf("2\n");
       if(nbr_link_quality[nbr_index][rss_count-1] < rss_val2){   // best oncoming neighbor : whom have less rss value due to more durable connection!
         rss_val2 = nbr_link_quality[nbr_index][rss_count-1] ; 
         output2 = candid_nbrs[i] ; //printf("%u\n", output2);
       }
       permission1 = 1 ;
       permission3 = 0 ;
       permission4 = 0 ;
     }
     if(permission3){//printf("3\n");
       if(rss_val3 <= nbr_link_quality[nbr_index][rss_count-1]){    // best neighbor in this section : whom have greater rss value 
         rss_val3 = nbr_link_quality[nbr_index][rss_count-1] ; 
         output3 = candid_nbrs[i] ; //printf("%u\n", output3);
       }
       permission1 = 1 ;
       permission2 = 1 ;
       permission4 = 0 ;
     }
     if(permission4){//printf("4\n");
       if(rss_val4 > nbr_link_quality[nbr_index][rss_count-1]){    // best oncoming neighbor : whom have less rss value due to more durable connection!
         rss_val4 = nbr_link_quality[nbr_index][rss_count-1] ; 
         output4 = candid_nbrs[i] ; //printf("%u\n", output4);
       }
       permission1 = 1 ;
       permission2 = 1 ;
       permission3 = 1 ;
     }
  }
  if(output1 > 0){/*printf("11\n");*/ return output1 ;}
  if(output2 > 0){/*printf("12\n");*/ return output2 ;}
  if(output3 > 0){/*printf("13\n");*/ return output3 ;}
  if(output4 > 0){/*printf("14\n");*/ return output4 ;}
//#endif
}

int index_of_nbrs(int node_id){
  int i = 0 ;
  for(i=0; i< nbr_count ; i++){
     if(nbrs[i] == node_id) {return i;}
  }
}

void dis_nbr_add(int a){
  int i = 0;
  for(i=0; i<3; i++){
    if(dis_nbr[i] == 0){break;}
  }
  if(i<3){dis_nbr[i] = a;}else{/*full*/}
}

int dis_nbr_lookup(int a){
  int i = 0;
  for(i=0; i<3 ; i++){
    if(dis_nbr[i]==a){return 1;}
  }
  return 0 ;
}

/*int candid_lookup(int node){
  if(node == 0){return 0;}
  int output = 0 ;
  int i = 0 ; 
  for(i=0 ; i < nbr_count ; i++){
     if(candid_nbrs[i] == node){output = 1;}
  }
  return output ;
}*/

/*int child_lookup(int node){
   if(node == 0){return 0;} // if the node was unknown return zero
   int output = 0;
   int i = 0 ;
   for(i = 0; i<nbr_count ; i++){
      if(children[i] == node){output = 1;}
   }
   return output;
}*/


/*.....................................................................................Amirreza.....*/


/** @}*/
