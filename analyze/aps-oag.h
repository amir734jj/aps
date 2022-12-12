#ifndef APS_OAG_H
#define APS_OAG_H

extern void compute_oag(Declaration,STATE *);

/** Return phase (synthesized) or -phase (inherited)
 * for fibered attribute, given the phylum's summary dependence graph.
 */
extern int attribute_schedule(PHY_GRAPH *phy_graph, FIBERED_ATTRIBUTE* key);

/** A conditional total order is a tree of cto nodes.
 * null means the CTO is done.
 *
 * If the instance is an if_rule, it will have two children
 * otherwise, just one.
 */
typedef struct cto_node CTO_NODE;

struct cto_node {
  CTO_NODE* cto_prev;
  INSTANCE* cto_instance;
  CTO_NODE* cto_next;
  CTO_NODE* cto_if_true;
#define cto_if_false cto_next
};

extern int oag_debug;
#define TOTAL_ORDER 1
#define DEBUG_ORDER 2
#define PROD_ORDER 4
#define PROD_ORDER_DEBUG 8
#define TYPE_3_DEBUG 16
#define DEBUG_ORDER_VERBOSE 32

#define CONDITION_IS_IMPOSSIBLE(cond) ((cond).positive & (cond).negative)
#define MERGED_CONDITION_IS_IMPOSSIBLE(cond1, cond2) (((cond1).positive|(cond2).positive) & ((cond1).negative|(cond2).negative))

CONDITION instance_condition(INSTANCE *in);

#endif
