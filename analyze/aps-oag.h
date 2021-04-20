extern void compute_oag(Declaration,STATE *);

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

// Scheduling groups
// 1) <-ph,nch> inh attr of parent
// 2) <+ph,nch> syn attr of parent
// 3) <ph,ch>   all attrs of child
// 4) <0,0>     for all locals and conditionals
#define KEY_SCHEDULE_GROUP1 1 
#define KEY_SCHEDULE_GROUP2 2
#define KEY_SCHEDULE_GROUP3 4
#define KEY_SCHEDULE_GROUP4 8

typedef struct child_phase_type CHILD_PHASE;

struct child_phase_type
{ 
  short ch; // How to indicate if no child -1
  short ph; // Phase 0 for local attribute and conditions, if 0 not in the group
};
