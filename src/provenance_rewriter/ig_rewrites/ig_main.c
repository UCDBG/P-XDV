/*-----------------------------------------------------------------------------
 *
 * ig_main.c
 *
 *
 *		AUTHOR: shemon & seokki
 *
 *
 *
 *-----------------------------------------------------------------------------
 */

#include "configuration/option.h"
#include "instrumentation/timing_instrumentation.h"
#include "provenance_rewriter/pi_cs_rewrites/pi_cs_main.h"
#include "provenance_rewriter/ig_rewrites/ig_main.h"
#include "provenance_rewriter/ig_rewrites/ig_functions.h"
#include "provenance_rewriter/prov_utility.h"
#include "utility/string_utils.h"
#include "model/query_operator/query_operator.h"
#include "model/query_operator/query_operator_model_checker.h"
#include "model/query_operator/operator_property.h"
#include "mem_manager/mem_mgr.h"
#include "log/logger.h"
#include "model/node/nodetype.h"
#include "provenance_rewriter/prov_schema.h"
#include "model/list/list.h"
#include "model/set/set.h"
#include "model/expression/expression.h"
#include "model/set/hashmap.h"
#include "parser/parser_jp.h"
#include "provenance_rewriter/transformation_rewrites/transformation_prov_main.h"
#include "provenance_rewriter/semiring_combiner/sc_main.h"
#include "provenance_rewriter/coarse_grained/coarse_grained_rewrite.h"


#define LOG_RESULT(mes,op) \
    do { \
        INFO_OP_LOG(mes,op); \
        DEBUG_NODE_BEATIFY_LOG(mes,op); \
    } while(0)

#define INDEX "i_"
#define IG_PREFIX "ig_"
#define VALUE_IG "value_"
#define INTEG_SUFFIX "_integ"
#define IG_RIGHT "right_"
#define IG_LEFT "left_"
#define ANNO_SUFFIX "_anno"
#define HAMMING_PREFIX "hamming_"
#define PATTERN_IG "pattern_IG"
#define TOTAL_IG "Total_IG"
//#define AVG_DIST "Average_Distance"
#define COVERAGE "coverage"
#define INFORMATIVENESS "informativeness"
#define PATTERNIG "pattern_IG"
#define FSCORE "f_score"
#define FSCORETOPK "fscoreTopK"
#define MINFSCORETOPK "minfscoreTopK"


static QueryOperator *rewriteIG_Operator (QueryOperator *op);
static QueryOperator *rewriteIG_Conversion (ProjectionOperator *op);
static QueryOperator *rewriteIG_Projection(ProjectionOperator *op);
static QueryOperator *rewriteIG_Selection(SelectionOperator *op);
static QueryOperator *rewriteIG_Join(JoinOperator *op);
static QueryOperator *rewriteIG_TableAccess(TableAccessOperator *op);
static ProjectionOperator *rewriteIG_SumExprs(ProjectionOperator *op);
static ProjectionOperator *rewriteIG_HammingFunctions(ProjectionOperator *op);

static Node *asOf;
static RelCount *nameState;
List *attrL = NIL;
List *attrR = NIL;

int tablePos = 0;

//int globalRightTableLen = 0;
static boolean explFlag;
static boolean igFlag;
static Node *topk;

QueryOperator *
rewriteIG (ProvenanceComputation  *op)
{
    START_TIMER("rewrite - IG rewrite");

    // unset relation name counters
    nameState = (RelCount *) NULL;
    DEBUG_NODE_BEATIFY_LOG("*************************************\nREWRITE INPUT\n"
            "******************************\n", op);

    //mark the number of table - used in provenance scratch
    markNumOfTableAccess((QueryOperator *) op);

    QueryOperator *newRoot = OP_LCHILD(op);
    DEBUG_NODE_BEATIFY_LOG("rewRoot is:", newRoot);

    igFlag = op->igFlag;
    explFlag = op->explFlag;
    topk = op->topk;

    // cache asOf
    asOf = op->asOf;

    // rewrite subquery under provenance computation
    rewriteIG_Operator(newRoot);
    DEBUG_NODE_BEATIFY_LOG("before rewritten query root is switched:", newRoot);

    // update root of rewritten subquery
    newRoot = OP_LCHILD(op);

    // adapt inputs of parents to remove provenance computation
    switchSubtrees((QueryOperator *) op, newRoot);
    DEBUG_NODE_BEATIFY_LOG("rewritten query root is:", newRoot);
    STOP_TIMER("rewrite - IG rewrite");

    return newRoot;
}

static QueryOperator *
rewriteIG_Operator (QueryOperator *op)
{
    QueryOperator *rewrittenOp;

    switch(op->type)
    {
    	case T_CastOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_SelectionOperator:
        	rewrittenOp = rewriteIG_Selection((SelectionOperator *) op);
        	break;
        case T_ProjectionOperator:
            rewrittenOp = rewriteIG_Projection((ProjectionOperator *) op);
            break;
        case T_AggregationOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_JoinOperator:
            rewrittenOp = rewriteIG_Join((JoinOperator *) op);
            break;
        case T_SetOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_TableAccessOperator:
            rewrittenOp = rewriteIG_TableAccess((TableAccessOperator *) op);
            break;
        case T_ConstRelOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_DuplicateRemoval:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_OrderOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_JsonTableOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_NestingOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        default:
            FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
            return NULL;
    }

    if (isRewriteOptionActivated(OPTION_AGGRESSIVE_MODEL_CHECKING)){
        ASSERT(checkModel(rewrittenOp));
    }
    DEBUG_NODE_BEATIFY_LOG("rewritten query operators:", rewrittenOp);
    return rewrittenOp;
}

static QueryOperator *
rewriteIG_Selection (SelectionOperator *op) //where clause
{
    ASSERT(OP_LCHILD(op));

    DEBUG_LOG("REWRITE-PICS - Selection");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    //add semiring options
    QueryOperator *child = OP_LCHILD(op);

    // store the join query
    SET_STRING_PROP(op, PROP_JOIN_OP_IG, OP_LCHILD(op));

    // rewrite child first
    List *inputProjExpr = (List *) GET_STRING_PROP(op,IG_INPUT_PROP);
    List *inputProjDefs = (List *) GET_STRING_PROP(op, IG_INPUT_DEFS_PROP);
    SET_STRING_PROP(OP_LCHILD(op), IG_INPUT_PROP, inputProjExpr);
	SET_STRING_PROP(OP_LCHILD(op), IG_INPUT_DEFS_PROP, inputProjDefs);
	SET_STRING_PROP(OP_LCHILD(op), PROP_WHERE_CLAUSE, op->cond);

    rewriteIG_Operator(child);

    SET_STRING_PROP(op, IG_L_PROP,
    			copyObject(GET_STRING_PROP(child, IG_L_PROP)));

    SET_STRING_PROP(op, IG_R_PROP,
    			copyObject(GET_STRING_PROP(child, IG_R_PROP)));


    // update selection
	Operator *cond = (Operator *) op->cond;

	FOREACH(Node, n, cond->args)
	{
		if(isA(n,AttributeReference))
		{
			AttributeReference *ar = (AttributeReference *) n;
			int attrPos = getAttrPos(child, ar->name);
			ar->attrPosition = attrPos;
		}

		if(isA(n,Operator))
		{
			Operator *o = (Operator *) n;
			FOREACH(Node, n, o->args)
			{
				if(isA(n,AttributeReference))
				{
					AttributeReference *ar = (AttributeReference *) n;
					int attrPos = getAttrPos(child, ar->name);
					ar->attrPosition = attrPos;
				}
			}
		}
	}

	op->op.schema->attrDefs = child->schema->attrDefs;

	// if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
	if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
	{
		SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING,
				copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
	}

    LOG_RESULT("Rewritten Selection Operator tree", op);
    return (QueryOperator *) op;
}

//rewriteIG_Conversion
static QueryOperator *
rewriteIG_Conversion (ProjectionOperator *op)
{

	// exprs to include for conversion only
	List *projExprs = NIL;
	List *attrNames = NIL;

	FOREACH(AttributeDef, a, op->op.schema->attrDefs)
	{

		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0,
						getAttrPos((QueryOperator *) op, a->attrName), 0, a->dataType));

		attrNames = appendToTailOfList(attrNames, a->attrName);
	}

	// create projection operator upon selection operator from select clause
	ProjectionOperator *po = createProjectionOp(projExprs, NULL, NIL, attrNames);
	po->projExprs = toAsciiList(po);

	addChildOperator((QueryOperator *) po, (QueryOperator *) op);
	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) op, (QueryOperator *) po);

	// Creating a new projection so
	// ascii(unnest(string_to_array(ig_conv_owned_county, NULL)))) does not end up in SUM function
	List *cleanExprs = NIL;
	List *cleanNames = NIL;

	FOREACH(AttributeDef, a, po->op.schema->attrDefs)
	{

		cleanExprs = appendToTailOfList(cleanExprs,
				createFullAttrReference(a->attrName, 0,
						getAttrPos((QueryOperator *) po, a->attrName), 0, a->dataType));

		cleanNames = appendToTailOfList(cleanNames, a->attrName);
	}

	//creating projection operator before aggregation op. This is NEEDED!
	ProjectionOperator *cleanpo = createProjectionOp(cleanExprs, NULL, NIL, cleanNames);
	addChildOperator((QueryOperator *) cleanpo, (QueryOperator *) po);
	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) po, (QueryOperator *) cleanpo);

	List *aggrs = NIL;
	List *groupBy = NIL;
	List *newNames = NIL;
	List *aggrNames = NIL;
	List *groupByNames = NIL;

	FOREACH(AttributeReference, n, po->projExprs)
	{
		if(isA(n, Ascii))
		{
			Ascii *ai = (Ascii *) n;
			Unnest *un = (Unnest *) ai->expr;
			StringToArray *sta = (StringToArray *) un->expr;
			AttributeReference *ar = (AttributeReference *) sta->expr;
			aggrNames = appendToTailOfList(aggrNames, ar->name);
		}
		else
		{
			if(isA(n, AttributeReference))
			{
				groupBy = appendToTailOfList(groupBy, n);
				groupByNames = appendToTailOfList(groupByNames, n->name);
			}

			if(isA(n, CastExpr))
			{
				CastExpr *ce = (CastExpr *) n;
				AttributeReference *ar = (AttributeReference *) ce->expr;
				groupBy = appendToTailOfList(groupBy, (Node *) ar);
			}
		}
	}

	newNames = CONCAT_LISTS(aggrNames, groupByNames);
	aggrs = getAsciiAggrs(po->projExprs);
	AggregationOperator *ao = createAggregationOp(aggrs , groupBy, NULL, NIL, newNames);
	//changing schema for string attributes
	FOREACH(AttributeDef, adef, ao->op.schema->attrDefs)
	{
		if(isPrefix(adef->attrName, "ig") && adef->dataType == DT_STRING)
		{
			adef->dataType = DT_INT;
		}
	}

	ProjectionOperator *addPo = NULL;
	//----------------------------------------
	//if ascii ar exist then att the aggregate operator
	if(hasAscii(po->projExprs) == 1)
	{
		addChildOperator((QueryOperator *) ao, (QueryOperator *) cleanpo);
		// Switch the subtree with this newly created projection operator.
		switchSubtrees((QueryOperator *) cleanpo, (QueryOperator *) ao);
		// CREATING THE NEW PROJECTION OPERATOR
		projExprs = NIL;
		projExprs = getARfromAttrDefs(ao->op.schema->attrDefs);

		//create projection operator upon selection operator from select clause
		ProjectionOperator *newPo = createProjectionOp(projExprs, NULL, NIL, newNames);

		addChildOperator((QueryOperator *) newPo, (QueryOperator *) ao);
		// Switch the subtree with this newly created projection operator.
		switchSubtrees((QueryOperator *) ao, (QueryOperator *) newPo);

		// CAST_EXPR
		List *newProjExprs = NIL;

		FOREACH(AttributeReference, a, newPo->projExprs)
		{
			if(isPrefix(a->name, "ig"))
			{

					CastExpr *castInt;
					CastExpr *cast;
					castInt = createCastExpr((Node *) a, DT_INT);
					cast = createCastExpr((Node *) castInt, DT_BIT10);

					newProjExprs = appendToTailOfList(newProjExprs, cast);
			}
			else
			{
				newProjExprs = appendToTailOfList(newProjExprs, a);
			}

		}

		newPo->projExprs = newProjExprs;

		// matching the datatype of attribute def in the projection
		FOREACH(AttributeDef, a, newPo->op.schema->attrDefs)
		{
			if(isPrefix(a->attrName,"ig"))
			{
				a->dataType = DT_BIT10;
			}
		}

	//	retrieve the original order of the projection attributes
		projExprs = NIL;
		newNames = NIL;

		projExprs = getARfromAttrDefswPos((QueryOperator *) newPo, po->op.schema->attrDefs);

		//TODO: duplicate function created
		newNames = getAttrNames(po->op.schema);

		addPo = createProjectionOp(projExprs, NULL, NIL, newNames);

		addChildOperator((QueryOperator *) addPo, (QueryOperator *) newPo);

		// Switch the subtree with this newly created projection operator.
		switchSubtrees((QueryOperator *) newPo, (QueryOperator *) addPo);


	}
	else if(hasAscii(po->projExprs) == 0)
	{
		// CAST_EXPR
		List *newProjExprs = NIL;

		FOREACH(AttributeReference, a, cleanpo->projExprs)
		{
			if(isPrefix(a->name, "ig"))
			{

					CastExpr *castInt;
					CastExpr *cast;
					castInt = createCastExpr((Node *) a, DT_INT);
					cast = createCastExpr((Node *) castInt, DT_BIT10);

					newProjExprs = appendToTailOfList(newProjExprs, cast);
			}
			else
			{
				newProjExprs = appendToTailOfList(newProjExprs, a);
			}

		}

		cleanpo->projExprs = newProjExprs;

		// matching the datatype of attribute def in the projection
		FOREACH(AttributeDef, a, cleanpo->op.schema->attrDefs)
		{
			if(isPrefix(a->attrName,"ig"))
			{
				a->dataType = DT_BIT10;
			}
		}

	//	retrieve the original order of the projection attributes
		projExprs = NIL;
		newNames = NIL;
		projExprs = getARfromAttrDefswPos((QueryOperator *) cleanpo, po->op.schema->attrDefs);
		//TODO: duplicate function created
		newNames = getAttrNames(po->op.schema);

		addPo = createProjectionOp(projExprs, NULL, NIL, newNames);

		addChildOperator((QueryOperator *) addPo, (QueryOperator *) cleanpo);

		// Switch the subtree with this newly created projection operator.
		switchSubtrees((QueryOperator *) cleanpo, (QueryOperator *) addPo);

	}
	LOG_RESULT("Converted Operator tree", addPo);
	return (QueryOperator *) addPo;
}

static ProjectionOperator *
rewriteIG_SumExprs (ProjectionOperator *hammingvalue_op)
{
    ASSERT(OP_LCHILD(hammingvalue_op));
    DEBUG_LOG("REWRITE-IG - Computing rowIG");
    DEBUG_LOG("Operator tree \n%s", nodeToString(hammingvalue_op));
	// Adding Sum Rows function
	int posV = 0;
	List *sumlist = NIL;
	Node *sumExpr = NULL;
	List *sumExprs = NIL;
	List *sumNames = NIL;

	FOREACH(AttributeDef, a, hammingvalue_op->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName, VALUE_IG))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			sumNames = appendToTailOfList(sumNames, a->attrName);
			sumlist = appendToTailOfList(sumlist, ar);
			posV++;
		}
		else
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			sumNames = appendToTailOfList(sumNames, a->attrName);
			posV++;
		}

	}

	sumExpr = (Node *) (createOpExpr("+", sumlist));
	sumExprs = appendToTailOfList(sumExprs, sumExpr);
	sumNames = appendToTailOfList(sumNames, strdup(TOTAL_IG));

	ProjectionOperator *sumrows = createProjectionOp(sumExprs, NULL, NIL, sumNames);

	addChildOperator((QueryOperator *) sumrows, (QueryOperator *) hammingvalue_op);
	switchSubtrees((QueryOperator *) hammingvalue_op, (QueryOperator *) sumrows);

    // store the join query
	SET_STRING_PROP(sumrows, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(hammingvalue_op, PROP_JOIN_OP_IG)));

	return sumrows;

}

//rewriteIG_HammingFunctions
static ProjectionOperator *
rewriteIG_HammingFunctions (ProjectionOperator *newProj)
{
    ASSERT(OP_LCHILD(newProj));
    DEBUG_LOG("REWRITE-IG - Hamming Computation");
    DEBUG_LOG("Operator tree \n%s", nodeToString(newProj));

    QueryOperator *child = OP_LCHILD(newProj);
    HashMap *nameToIgAttrOpp = NEW_MAP(Constant, Node);
    HashMap *nameToIgAttrRef = NEW_MAP(Constant, Node);

    // collect corresponding attributes of owned data
//    int pos = 0;

    FOREACH(AttributeDef,a,attrL)
	{
    	if(isPrefix(a->attrName,IG_PREFIX))
    	{
    		//TODO: search corresponding attributes
//    		AttributeDef *ar = (AttributeDef *) getNthOfListP(attrR,pos);
//    		char *corrAttrName = ar->attrName;
    		char *leftIgName = replaceSubstr(a->attrName, IG_LEFT, "");

			FOREACH(AttributeDef, adr, attrR)
    		{
				char *rightIgName = replaceSubstr(adr->attrName, IG_RIGHT, "");

				if(streq(leftIgName, rightIgName))
				{
		    		// store the corresponding ig attribute names in shared
//		    		Node *arRef = (Node *) getAttrRefByName((QueryOperator *) child, corrAttrName);
					Node *arRef = (Node *) getAttrRefByName((QueryOperator *) child, adr->attrName);
		    		MAP_ADD_STRING_KEY(nameToIgAttrOpp, a->attrName, arRef);
				}
    		}

    		// store the ig attributes' reference
    		Node *aRef = (Node *) getAttrRefByName((QueryOperator *) child, a->attrName);
			MAP_ADD_STRING_KEY(nameToIgAttrRef, a->attrName, aRef);
    	}

//    	pos++;
	}

    // collect corresponding attributes of shared data
//    pos = 0;

    FOREACH(AttributeDef,a,attrR)
	{
    	if(isPrefix(a->attrName,IG_PREFIX))
    	{

			//TODO: search corresponding attributes
//			AttributeDef *al = (AttributeDef *) getNthOfListP(attrL,pos);
//			char *corrAttrName = al->attrName;
    		char *rightIgName = replaceSubstr(a->attrName, IG_RIGHT, "");

    		FOREACH(AttributeDef, adl, attrL)
			{
				char *leftIgName = replaceSubstr(adl->attrName, IG_LEFT, "");

				if(streq(leftIgName, rightIgName))
				{
					// store the corresponding ig attribute names in shared
//					Node *alRef = (Node *) getAttrRefByName((QueryOperator *) child, corrAttrName);
					Node *alRef = (Node *) getAttrRefByName((QueryOperator *) child, adl->attrName);
					MAP_ADD_STRING_KEY(nameToIgAttrOpp, a->attrName, alRef);
				}
			}

			// store the ig attributes' reference
			Node *aRef = (Node *) getAttrRefByName((QueryOperator *) child, a->attrName);
			MAP_ADD_STRING_KEY(nameToIgAttrRef, a->attrName, aRef);
    	}

//    	pos++;
	}


    // create provenance columns using case when
    List *commonAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_NON_JOIN_COMMON_ATTR_R);
//	List *joinAttrNames = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_JOIN_ATTR);
	List *joinAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_JOIN_ATTR_R);
	List *newProjExprs = NIL;
	int pos = 0;

    FOREACH(AttributeDef, a, newProj->op.schema->attrDefs)
    {
		Node *n = (Node *) getNthOfListP(newProj->projExprs,pos);
		AttributeReference *origIgInteg = NULL;

		Node *cond = NULL;
		Node *then = NULL;
		Node *els = NULL;
		CaseWhen *caseWhen = NULL;
		CaseExpr *caseExpr = NULL;

    	// search corresponding attribute for integ ig column
    	if(isPrefix(a->attrName,IG_PREFIX))
    	{
    		if(isSuffix(a->attrName,INTEG_SUFFIX))
    		{
    			/*
    			 *  As long as its suffix is "_integ", the attributes must be input to the hamming computation.
    			 *  Because conversion already takes care of what attributes should be the input to the hamming computation.
    			 */
        		if(isA(n, AttributeReference))
        		{
        			origIgInteg = (AttributeReference *) n;
//            		char *igOrigNameInteg = origIgInteg->name; //not used
            		char *igOrigNameWithoutInteg = replaceSubstr(origIgInteg->name, INTEG_SUFFIX, "");

            		if(MAP_HAS_STRING_KEY(nameToIgAttrOpp, igOrigNameWithoutInteg))
        			{
        				AttributeReference *corrIgExpr =
        						(AttributeReference *) MAP_GET_STRING(nameToIgAttrOpp, igOrigNameWithoutInteg);

        				// for join attributes
        				// TODO: creating constant depends on the data type of igOrigNameInteg
//        				if(searchListNode(joinAttrNames, (Node *) createConstString(igOrigNameInteg)))
//        				if(searchListNode(joinAttrNames, (Node *) a))
//        				{
        					// Same here. Falling into this case means that the attribute is not join attribute and is coming from shared
        					cond = (Node *) createIsNullExpr((Node *) origIgInteg);
        					then = (Node *) corrIgExpr;
        					els = (Node *) origIgInteg;

        					caseWhen = createCaseWhen(cond, then);
        					caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//        				}
//        				else
//        				{
//							cond = (Node *) createIsNullExpr((Node *) origIgInteg);
//							then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
//							els = (Node *) origIgInteg;
//
//							caseWhen = createCaseWhen(cond, then);
//							caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//        				}
        			}
            		else // if the corresponding ig attribute does not exist
            		{
						cond = (Node *) createIsNullExpr((Node *) origIgInteg);
						then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
						els = (Node *) origIgInteg;

						caseWhen = createCaseWhen(cond, then);
						caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
            		}

            		newProjExprs = appendToTailOfList(newProjExprs,caseExpr);

        		}
        		else
        		{
        			if(isA(n,CaseExpr)) {

        				CaseExpr *ce = (CaseExpr *) n;
        				CaseWhen *cw = (CaseWhen *) getHeadOfListP(ce->whenClauses);
        				Node *then = (Node *) cw->then;
            			Node *castExpr = (Node *) createCastExpr(then, DT_BIT10);
            			cw->then = castExpr;
        			}

        	    	newProjExprs = appendToTailOfList(newProjExprs,n);
        		}
    		}

        	// apply case when for original ig columns
        	if(!isSuffix(a->attrName,INTEG_SUFFIX))
        	{
        		origIgInteg = (AttributeReference *) n;
        		char *igOrigNameInteg = origIgInteg->name;

        		// ig attributes from shared
//        		if(searchListNode(commonAttrNamesR, (Node *) createConstString(igOrigNameInteg)) ||
//        				searchListNode(joinAttrNamesR, (Node *) createConstString(igOrigNameInteg)))
				if(searchListNode(commonAttrNamesR, (Node *) a) ||
						searchListNode(joinAttrNamesR, (Node *) a))
        		{
        			AttributeReference *corrIgExpr =
        					(AttributeReference *) MAP_GET_STRING(nameToIgAttrOpp, igOrigNameInteg);

    				cond = (Node *) createIsNullExpr((Node *) origIgInteg);
    				then = (Node *) corrIgExpr;
    				els = (Node *) origIgInteg;

    				caseWhen = createCaseWhen(cond, then);
    				caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
        		}
        		// either ig attributes from owned or non-common attributes
        		else
        		{
    				cond = (Node *) createIsNullExpr((Node *) origIgInteg);
    				then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
    				els = (Node *) origIgInteg;

    				caseWhen = createCaseWhen(cond, then);
    				caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
        		}

				newProjExprs = appendToTailOfList(newProjExprs,caseExpr);
        	}
    	}
    	else
        	newProjExprs = appendToTailOfList(newProjExprs,n);

    	pos++;
    }

    // replace project exprs with new project exprs
    newProj->projExprs = newProjExprs;
    INFO_OP_LOG("Rewritten tree having provenance attributes", newProj);

    // Adding hammingDist function
    List *exprs = NIL;
    List *atNames = NIL;
    int x = 0;

    FOREACH(AttributeDef, a, newProj->op.schema->attrDefs)
	{
    	//commenting out IG attributes here to keep outputs clean
    	if(isPrefix(a->attrName, IG_PREFIX))
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, DT_BIT10);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
//    		continue;
    	}
    	else if(isSuffix(a->attrName, INTEG_SUFFIX))
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, DT_BIT10);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
    	}
    	else
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, a->dataType);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
    	}
    	x++;
	}


	List *igAttrL = NIL; // ig_left
	List *cleanigAttrL = NIL; // ig_left_integ
	List *cleanigAttrR = NIL; // ig_right_integ

	//input query attributes
	List *origAttrs = NIL;

	//original attribute references
	FOREACH(AttributeDef, n, newProj->op.schema->attrDefs)
	{
		if(!isPrefix(n->attrName, IG_PREFIX))
		{
			AttributeReference *ar = getAttrRefByName((QueryOperator *) newProj, n->attrName);
			origAttrs = appendToTailOfList(origAttrs, ar);
		}
	}

	FOREACH(AttributeDef, n, newProj->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, IG_PREFIX))
		{
			if(isSuffix(n->attrName, INTEG_SUFFIX))
			{
				if(isSubstr(n->attrName, IG_RIGHT))
				{
					AttributeReference *arInteg = getAttrRefByName((QueryOperator *) newProj, n->attrName);
					cleanigAttrR = appendToTailOfList(cleanigAttrR, arInteg);
				}

				if(isSubstr(n->attrName, IG_LEFT))
				{
					AttributeReference *arl = getAttrRefByName((QueryOperator *) newProj, n->attrName);
					cleanigAttrL = appendToTailOfList(cleanigAttrL, arl);
				}
			}
			else
			{
				if(isSubstr(n->attrName, IG_LEFT))
				{
					AttributeReference *arl = getAttrRefByName((QueryOperator *) newProj, n->attrName);
					igAttrL = appendToTailOfList(igAttrL, arl);
				}
			}

//			if (isSubstr(n->attrName, "left") && !isSuffix(n->attrName, INTEG_SUFFIX)
////					&& isSubstr(n->attrName, "right") == FALSE
//			)
//			{
//				FOREACH(AttributeReference, ar, origAttrs)
//				{
//					if(isSubstr(n->attrName, ar->name) == TRUE)
//					{
//						AttributeReference *ar = getAttrRefByName((QueryOperator *) newProj, n->attrName);
//						igAttrL = appendToTailOfList(igAttrL, ar);
//					}
//				}
//			}
//
//			if (isSubstr(n->attrName, "integ") == TRUE)
//			{
//				FOREACH(AttributeReference, ar, origAttrs)
//				{
//					if(isSubstr(n->attrName, ar->name) == TRUE)
//					{
//						AttributeReference *arn = getAttrRefByName((QueryOperator *) newProj, n->attrName);
//						cleanigAttrR = appendToTailOfList(cleanigAttrR, arn);
//					}
//				}
//			}
		}
	}

//	List *igAttrR = removeDupeAr(cleanigAttrR);
//	int LL = LIST_LENGTH(igAttrL);
//	int RR = LIST_LENGTH(igAttrR);
//	int lend = 1;
//	int rend = 1;

	// 1. hamming function for all same/common attributes first
	// 2. renaming the attribute names || Keeping the table Names for now

	FOREACH(AttributeReference, arR, cleanigAttrR)
	{
		List* cast = NIL;
		char* arRname = replaceSubstr(arR->name, INTEG_SUFFIX, "");

		if(MAP_HAS_STRING_KEY(nameToIgAttrOpp, arRname))
		{
			CastExpr *castL;
			CastExpr *castR;

			AttributeReference *ar = (AttributeReference *) MAP_GET_STRING(nameToIgAttrOpp, arRname);
			AttributeReference *arL = getAttrRefByName((QueryOperator *) newProj, ar->name);

			castL = createCastExpr((Node *) arL, DT_STRING);
			castR = createCastExpr((Node *) arR, DT_STRING);
			cast = LIST_MAKE(castL, castR);

			FunctionCall *hammingdist = createFunctionCall("hammingxor", cast);
			exprs = appendToTailOfList(exprs, hammingdist);

			char *name = CONCAT_STRINGS(HAMMING_PREFIX, substr(arR->name, 8 , strlen(arR->name) - 1));
			atNames = appendToTailOfList(atNames, name);
		}
		else
		{
			CastExpr *castR = createCastExpr((Node *) arR, DT_STRING);
			cast = LIST_MAKE(createConstString("0000000000"), castR);

			FunctionCall *hammingdist = createFunctionCall("hammingxor", cast);
			exprs = appendToTailOfList(exprs,hammingdist);

			char *name = CONCAT_STRINGS(HAMMING_PREFIX, substr(arR->name, 8 , strlen(arR->name) - 1));
			atNames = appendToTailOfList(atNames, name);
		}
	}

// OUTDATED CODES
//	FOREACH(AttributeReference, arR, igAttrR)
//	{
//		List *cast = NIL;
//		lend = 1;
//		FOREACH(AttributeReference, arL, igAttrL)
//		{
//			//FOR SAME ATTRIBUTES
//			if(isSubstr(arR->name, arL->name) == TRUE)
//			{
//				CastExpr *castL;
//				CastExpr *castR;
//				castL = createCastExpr((Node *) arL, DT_STRING);
//				castR = createCastExpr((Node *) arR, DT_STRING);
//				cast = LIST_MAKE(castL, castR);
//				FunctionCall *hammingdist = createFunctionCall("hammingxor", cast);
//				exprs = appendToTailOfList(exprs,hammingdist);
//				char *name = CONCAT_STRINGS(HAMMING_PREFIX, substr(arR->name, 8 , strlen(arR->name) - 1));
//				atNames = appendToTailOfList(atNames, name);
//				break;
//			}
//			//UNIQUE ATTRIBUTES FROM R
//			else if(lend >= LL)
//			{
//				CastExpr *castR;
//				castR = createCastExpr((Node *) arR, DT_STRING);
//				cast = LIST_MAKE(createConstString("0000000000"), castR);
//				FunctionCall *hammingdist = createFunctionCall("hammingxor", cast);
//				exprs = appendToTailOfList(exprs,hammingdist);
//				char *name = CONCAT_STRINGS(HAMMING_PREFIX, substr(arR->name, 8 , strlen(arR->name) - 1));
//				atNames = appendToTailOfList(atNames, name);
//			}
//			else
//			{
//				lend = lend + 1;
//			}
//
//		}
//	}

	//UNIQUE IG_INTEG ATTRIBUTES FROM L
	FOREACH(AttributeReference, arL, cleanigAttrL)
	{
		List *cast = NIL;

		FOREACH(AttributeReference, arLOrig, igAttrL)
		{
			if(isSubstr(arL->name, arLOrig->name))
			{
				CastExpr *castL = createCastExpr((Node *) arLOrig, DT_STRING);
				CastExpr *castR = createCastExpr((Node *) arL, DT_STRING);
				cast = LIST_MAKE(castL, castR);

				FunctionCall *hammingdist = createFunctionCall("hammingxor", cast);
				exprs = appendToTailOfList(exprs, hammingdist);

				char *name = CONCAT_STRINGS(HAMMING_PREFIX, substr(arL->name, 8 , strlen(arL->name) - 1));
				atNames = appendToTailOfList(atNames, name);
			}
		}
	}

//	FOREACH(AttributeReference, arL, igAttrL)
//	{
//		List *cast = NIL;
//		rend = 1;
//		FOREACH(AttributeReference, arR, igAttrR)
//		{
//			if(isSubstr(arR->name, arL->name) == TRUE)
//			{
//				break;
//			}
//			else if(rend >= RR)
//			{
//				CastExpr *castL;
//				castL = createCastExpr((Node *) arL, DT_STRING);
//				cast = LIST_MAKE(createConstString("0000000000"), castL);
//				FunctionCall *hammingdist = createFunctionCall("hammingxor", cast);
//				exprs = appendToTailOfList(exprs,hammingdist);
//				char *name = CONCAT_STRINGS(HAMMING_PREFIX, substr(arL->name, 8 , strlen(arL->name) - 1));
//				atNames = appendToTailOfList(atNames, name);
//			}
//			else
//			{
//				rend = rend + 1;
//			}
//
//		}
//	}

	ProjectionOperator *hamming_op = createProjectionOp(exprs, NULL, NIL, atNames);

	FOREACH(AttributeDef, n, hamming_op->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, HAMMING_PREFIX))
		{
			n->dataType = DT_STRING;
		}
	}

	FOREACH(AttributeReference, n, hamming_op->projExprs)
	{
		if(isPrefix(n->name, HAMMING_PREFIX))
		{
			n->attrType = DT_STRING;
		}
	}

	FOREACH(AttributeReference, n, hamming_op->projExprs)
	{
		if(isA(n, FunctionCall))
		{
			FunctionCall *x = (FunctionCall *) n;
			x->isDistinct = FALSE;

		}
	}

    addChildOperator((QueryOperator *) hamming_op, (QueryOperator *) newProj);
    switchSubtrees((QueryOperator *) newProj, (QueryOperator *) hamming_op);
    INFO_OP_LOG("Rewritten tree for hamming distance", hamming_op);

    if(HAS_STRING_PROP(newProj, IG_PROP_ORIG_ATTR))
	{
		SET_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR,
				copyObject(GET_STRING_PROP(newProj, IG_PROP_ORIG_ATTR)));
	}

    // store the join query
	SET_STRING_PROP(hamming_op, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(newProj, PROP_JOIN_OP_IG)));


    //Adding hammingdistvalue function
	List *h_valueExprs = NIL;
	List *h_valueName = NIL;
	int posV = 0;

	FOREACH(AttributeDef, a, hamming_op->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName, HAMMING_PREFIX))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			h_valueExprs = appendToTailOfList(h_valueExprs, ar);
			h_valueName = appendToTailOfList(h_valueName, a->attrName);
		}
		else
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			h_valueExprs = appendToTailOfList(h_valueExprs, ar);
			h_valueName = appendToTailOfList(h_valueName, a->attrName);
		}

		posV++;
	}

	posV = 0;
	List *newExprs = copyObject(h_valueExprs);

	FOREACH(AttributeReference, a, newExprs)
	{
		if(isPrefix(a->name, HAMMING_PREFIX))
		{
			FunctionCall *hammingdistvalue = createFunctionCall("hammingxorvalue", singleton(a));
			h_valueExprs = appendToTailOfList(h_valueExprs, hammingdistvalue);
			char *name = CONCAT_STRINGS(VALUE_IG ,substr(a->name, 8, strlen(a->name) - 1));
			h_valueName = appendToTailOfList(h_valueName, name);
		}

		posV++;
	}

	ProjectionOperator *hammingvalue_op = createProjectionOp(h_valueExprs, NULL, NIL, h_valueName);

	FOREACH(AttributeDef, n, hammingvalue_op->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, VALUE_IG))
		{
			n->dataType = DT_INT;
		}
	}

	FOREACH(AttributeReference, n, hammingvalue_op->projExprs)
	{
		if(isPrefix(n->name, VALUE_IG))
		{
			n->attrType = DT_INT;
		}
	}

	addChildOperator((QueryOperator *) hammingvalue_op, (QueryOperator *) hamming_op);
	switchSubtrees((QueryOperator *) hamming_op, (QueryOperator *) hammingvalue_op);

    if(HAS_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR))
	{
		SET_STRING_PROP(hammingvalue_op, IG_PROP_ORIG_ATTR,
				copyObject(GET_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR)));
	}

    // store the join query
	SET_STRING_PROP(hammingvalue_op, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(hamming_op, PROP_JOIN_OP_IG)));

	return hammingvalue_op;
}

static AggregationOperator *
rewriteIG_PatternGeneration (ProjectionOperator *sumrows)
{

	ASSERT(OP_LCHILD(sumrows));
	DEBUG_LOG("REWRITE-IG - Pattern Generation");
	DEBUG_LOG("Operator tree \n%s", nodeToString(sumrows));

	List *Laggrs = NIL;;
	List *Raggrs = NIL;
	List *LaggrsNames = NIL;
	List *RaggrsNames = NIL;

	FOREACH(AttributeDef, n, attrL)
	{
		if(!isPrefix(n->attrName, IG_PREFIX))
		{
			if(!isSuffix(n->attrName, ANNO_SUFFIX))
			{
				Laggrs = appendToTailOfList(Laggrs, n);
				LaggrsNames = appendToTailOfList(LaggrsNames, n->attrName);
			}
		}
	}

	FOREACH(AttributeDef, n, attrR)
	{
		if(!isPrefix(n->attrName, IG_PREFIX))
		{
			if(!isSuffix(n->attrName, ANNO_SUFFIX))
			{
				Raggrs = appendToTailOfList(Raggrs, n);
				RaggrsNames = appendToTailOfList(RaggrsNames, n->attrName);
			}
		}
	}

	List *cleanExprs = NIL;
	List *cleanNames = NIL;

	//Creating Left Case when statements
	FOREACH(AttributeDef, L, Laggrs)
	{

		if(searchListString(RaggrsNames, L->attrName))
		{
			FOREACH(AttributeDef, R, Raggrs)
			{
				char *LAttrName = L->attrName;

				if(streq(L->attrName, R->attrName))
				{
					AttributeReference * arL = createFullAttrReference(LAttrName, 0,
							getAttrPos((QueryOperator *) sumrows, LAttrName),0, L->dataType);

					//TODO: search attributes from shared
					if(arL->attrPosition == -1)
					{
						LAttrName = CONCAT_STRINGS(L->attrName,gprom_itoa(1));
						arL->name = LAttrName;
						arL->attrPosition = getAttrPos((QueryOperator *) sumrows, LAttrName);

					}


					if(arL->attrPosition != -1)
					{
						cleanExprs = appendToTailOfList(cleanExprs, arL);
						cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, LAttrName));
					}
				}

			}
		}
		else
		{
			AttributeReference * arL = createFullAttrReference(L->attrName, 0,
					getAttrPos((QueryOperator *) sumrows, L->attrName),0, L->dataType);
			cleanExprs = appendToTailOfList(cleanExprs, arL);
			cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, L->attrName));
		}
	}


	FOREACH(AttributeDef, R, Raggrs)
	{
		if(!searchListString(LaggrsNames, R->attrName))
		{
			AttributeReference * arR = createFullAttrReference(R->attrName, 0,
					getAttrPos((QueryOperator *) sumrows, R->attrName),0, R->dataType);

			cleanExprs = appendToTailOfList(cleanExprs, arR);
			cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, R->attrName));

		}
	}

	// add ig columns and rowIG
	FOREACH(AttributeReference, n, sumrows->projExprs)
	{
		if(isPrefix(n->name, VALUE_IG))
		{
			cleanExprs = appendToTailOfList(cleanExprs,n);
			cleanNames = appendToTailOfList(cleanNames, n->name);
		}
	}

	FOREACH(AttributeDef, a, sumrows->op.schema->attrDefs)
	{
		if(streq(a->attrName,TOTAL_IG))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
					getAttrPos((QueryOperator *) sumrows, a->attrName), 0, a->dataType);

			cleanExprs = appendToTailOfList(cleanExprs,ar);
			cleanNames = appendToTailOfList(cleanNames, ar->name);
		}
	}

	ProjectionOperator *clean1 = createProjectionOp(cleanExprs, NULL, NIL, cleanNames);

	List *cleanExprs1 = NIL;
	List *cleanNames1 = NIL;
	List *origAttrs = NIL;

	FOREACH(AttributeDef, adef, sumrows->op.schema->attrDefs)
	{
		if(!isPrefix(adef->attrName, "hamming") && !isPrefix(adef->attrName, "value")
				&& !isPrefix(adef->attrName, "Total"))
		{
			AttributeReference *ar = getAttrRefByName((QueryOperator *) sumrows, adef->attrName);
			origAttrs = appendToTailOfList(origAttrs, ar);
		}
	}

	//cleaning up extra attributes from clean
	FOREACH(AttributeReference, ar , clean1->projExprs)
	{
		if(!isPrefix(ar->name, "value") && !isPrefix(ar->name, "Total"))
		{
			FOREACH(AttributeReference, oar, origAttrs)
			{
				if(streq(ar->name, oar->name))
				{
					cleanExprs1 = appendToTailOfList(cleanExprs1, ar);
					cleanNames1 = appendToTailOfList(cleanNames1, CONCAT_STRINGS(INDEX, ar->name));
				}
			}
		}
		else
		{
			cleanExprs1 = appendToTailOfList(cleanExprs1, ar);
			cleanNames1 = appendToTailOfList(cleanNames1, ar->name);
		}
	}

	ProjectionOperator *clean = createProjectionOp(cleanExprs1, NULL, NIL, cleanNames1);
	addChildOperator((QueryOperator *) clean, (QueryOperator *) sumrows);
	switchSubtrees((QueryOperator *) sumrows, (QueryOperator *) clean);


	List *projNames = NIL;
	List *groupBy = NIL;
	List *aggrs = NIL;
	FunctionCall *sum = NULL;

	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
	{
		//this one makes pattern_IG
		if(streq(n->attrName, TOTAL_IG))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
					   				 getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType);
			sum = createFunctionCall("SUM", singleton(ar));
			sum->isAgg = TRUE;

			aggrs = appendToTailOfList(aggrs,sum);
			projNames = appendToTailOfList(projNames, strdup(PATTERN_IG));
		}
	}

	// coverage
	Constant *countProv = createConstInt(1);
	FunctionCall *count = createFunctionCall("COUNT", singleton(countProv));
	count->isAgg = TRUE;

	aggrs = appendToTailOfList(aggrs,count);
	projNames = appendToTailOfList(projNames, strdup(COVERAGE));

	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, strdup(INDEX)))
		{
			groupBy = appendToTailOfList(groupBy,
					  createFullAttrReference(n->attrName, 0,
					  getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType));

			projNames = appendToTailOfList(projNames, n->attrName);

		}
	}

	AggregationOperator *ao = createAggregationOp(aggrs, groupBy, (QueryOperator *) clean, NIL, projNames);
	ao->isCube = TRUE;
	ao->isCubeTestList = (Node *) createConstInt(1);


	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(streq(n->attrName, strdup(PATTERN_IG)) ||
				streq(n->attrName, strdup(COVERAGE)))
		{
			n->dataType = DT_FLOAT;
		}
	}

	addParent((QueryOperator *) clean, (QueryOperator *) ao);
	switchSubtrees((QueryOperator *) clean, (QueryOperator *) ao);

	// Adding projection for Informativeness
	List *informExprs = NIL;
	List *informNames = NIL;

	int pos = 0;

	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{
			informExprs = appendToTailOfList(informExprs,
					  	  createFullAttrReference(n->attrName, 0,
					  			  pos, 0, n->dataType));
			informNames = appendToTailOfList(informNames, n->attrName);
		}

		pos++;
	}


	pos = 0;

	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(streq(n->attrName, PATTERN_IG) ||
				streq(n->attrName, COVERAGE))
		{
			// Adding patern_IG in the new informProj
			informExprs = appendToTailOfList(informExprs,
						  createFullAttrReference(n->attrName, 0,
								  pos, 0, n->dataType));
			informNames = appendToTailOfList(informNames, n->attrName);
		}

		pos++;
	}


	// ADDING INFORMATIVENESS
	pos = 0;
	List *sumExprs = NIL;
	Node *sumExpr = NULL;

	FOREACH(AttributeDef, n , ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{

			AttributeReference *ar = createFullAttrReference(n->attrName, 0, pos, 0, n->dataType);

			Node *cond = (Node *) createOpExpr(OPNAME_NOT, singleton(createIsNullExpr((Node *) ar)));
			Node *then = (Node *) (createConstInt(1));
			Node *els = (Node *) (createConstInt(0));


			CaseWhen *caseWhen = createCaseWhen(cond, then);
			CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

			sumExprs = appendToTailOfList(sumExprs, caseExpr);
		}

		pos++;

	}

	sumExpr = (Node *) (createOpExpr("+", sumExprs));
	informExprs = appendToTailOfList(informExprs, sumExpr);
	informNames = appendToTailOfList(informNames, strdup(INFORMATIVENESS));

	ProjectionOperator *inform = createProjectionOp(informExprs, (QueryOperator *) ao, NIL, informNames);
	addParent((QueryOperator *) ao, (QueryOperator *) inform);
	switchSubtrees((QueryOperator *) ao, (QueryOperator *) inform);

	INFO_OP_LOG("Generate Patterns While Computing Informativeness and Coverage: ", inform);

	int num_i = 0;

	// counting attributes
	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{
			num_i = num_i + 1;
		}
	}

	AttributeReference *cov = getAttrRefByName((QueryOperator *) inform, COVERAGE);
	AttributeReference *inf = getAttrRefByName((QueryOperator *) inform, INFORMATIVENESS);
	AttributeReference *pattIG = getAttrRefByName((QueryOperator *) inform, PATTERNIG);

	//creating where condition coverage > 1 OR (coverage = 1 AND informativeness = 5)
	//coverage > 1
	Node *covgt1 = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(cov, createConstInt(1)));

	//coverage = 1
	Node *cov1 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(cov, createConstInt(1)));

	//informativeness = 5
	Node *info5 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(inf, createConstInt(num_i)));

	//coverage = 1 AND informativeness = 5
	Node *subcond = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(cov1,info5));

	//coverage > 1 OR (coverage = 1 AND informativeness = 5)
	Node *cond = (Node *) createOpExpr(OPNAME_OR, LIST_MAKE(covgt1,subcond));

	//creating patternIG > 0
	Node *pattCondt = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(pattIG, createConstInt(0)));

	//patternIG > 0 AND coverage > 1 OR (coverage = 1 AND informativeness = 5)
	Node *finalCond = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(pattCondt, cond));

	// this one has removeNoGoodPatt
	SelectionOperator *removeNoGoodPatt = createSelectionOp(finalCond,
			(QueryOperator *) inform, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) inform, (QueryOperator *) removeNoGoodPatt);
	switchSubtrees((QueryOperator *) inform, (QueryOperator *) removeNoGoodPatt);

	INFO_OP_LOG("Remove No Good Patterns: ", removeNoGoodPatt);

	//creating topKPattConstPlac
	//where coverage > 1 and informativeness < 5
	//informativeness < 5
	Node *infoLess = (Node *) createOpExpr(OPNAME_LT, LIST_MAKE(inf, createConstInt(num_i)));

	//coverage > 1 and informativeness < 5
	Node *condtopKPattConstPlac = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(covgt1, infoLess));

	//creating topKPattConstPlac
	QueryOperator *cpRemoveNoGoodPatt = (QueryOperator *) removeNoGoodPatt;

	SelectionOperator *topKPattConstPlac = createSelectionOp(condtopKPattConstPlac,
			cpRemoveNoGoodPatt, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) cpRemoveNoGoodPatt, (QueryOperator *) topKPattConstPlac);
	switchSubtrees((QueryOperator *) cpRemoveNoGoodPatt, (QueryOperator *) topKPattConstPlac);

	INFO_OP_LOG("Patterns with Constants and Placeholders: ", topKPattConstPlac);

	//creating topKPattOnlyConst
	//subcond : coverage = 1 AND informativeness = 5

	QueryOperator *coRemoveNoGoodPatt = (QueryOperator *) copyObject((QueryOperator *) removeNoGoodPatt);
	SelectionOperator *topKPattOnlyConst = createSelectionOp(subcond, coRemoveNoGoodPatt, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) coRemoveNoGoodPatt, (QueryOperator *) topKPattOnlyConst);
	switchSubtrees((QueryOperator *) coRemoveNoGoodPatt, (QueryOperator *) topKPattOnlyConst);

	INFO_OP_LOG("Patterns with Only Placeholders: ", topKPattOnlyConst);



	List *topKattr = NIL;
	List *topKattrNames = NIL;
	List *inputTopK = NIL;
	int topKpos = 0;
	//pattern_IG | informativeness | coverage
	FOREACH(AttributeDef, n, topKPattConstPlac->op.schema->attrDefs)
	{
		if((!streq(n->attrName, INFORMATIVENESS)) &&
		   (!streq(n->attrName, COVERAGE)) &&
		   (!streq(n->attrName, PATTERNIG)))
		{
		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
		topKattr = appendToTailOfList(topKattr, ar);
		topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
		topKpos = topKpos + 1;
		}

		else if(streq(n->attrName, INFORMATIVENESS))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
			topKattr = appendToTailOfList(topKattr, ar);
			topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
			inputTopK = appendToTailOfList(inputTopK, ar);
			topKpos = topKpos + 1;
		}
		else if(streq(n->attrName, COVERAGE))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
			topKattr = appendToTailOfList(topKattr, ar);
			topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
			inputTopK = appendToTailOfList(inputTopK, ar);
			topKpos = topKpos + 1;
		}
		else if(streq(n->attrName, PATTERNIG))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
			topKattr = appendToTailOfList(topKattr, ar);
			topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
			inputTopK = appendToTailOfList(inputTopK, ar);
			topKpos = topKpos + 1;
		}
	}

	//patternIG * coverage * informativeness
	Node *prodK = (Node *) (createOpExpr(OPNAME_MULT, inputTopK));

	//3 * patternIG * coverage * informativeness
	Node *prod3K = (Node *) (createOpExpr(OPNAME_MULT, LIST_MAKE(createConstInt(3), prodK)));

	//patternIG + coverage + informativeness
	Node *sumOpK = (Node *) (createOpExpr(OPNAME_ADD, inputTopK));

	//3 * (patternIG * coverage * informativeness) / (patternIG + coverage + informativeness)
	Node *fscoreTopK = (Node *) (createOpExpr(OPNAME_DIV, LIST_MAKE(prod3K, sumOpK)));

	// string to float
	CastExpr *cast = createCastExpr(fscoreTopK, DT_FLOAT);

	topKattr = appendToTailOfList(topKattr, cast);
	topKattrNames = appendToTailOfList(topKattrNames, FSCORETOPK);

	//fscoreTopK
	ProjectionOperator *fscoreTopKOp = createProjectionOp(topKattr,
			(QueryOperator *) topKPattConstPlac, NIL, topKattrNames);

	addParent((QueryOperator *) topKPattConstPlac, (QueryOperator *) fscoreTopKOp);
	switchSubtrees((QueryOperator *) topKPattConstPlac, (QueryOperator *) fscoreTopKOp);

	// add projection for order by
	List *oExprs = NIL;
	int oPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, oPos, 0, a->dataType);
		oExprs = appendToTailOfList(oExprs, ar);

		oPos++;
	}

	ProjectionOperator *orderPo = createProjectionOp(oExprs,
			(QueryOperator *) fscoreTopKOp, NIL, getAttrNames(fscoreTopKOp->op.schema));

	addParent((QueryOperator *) fscoreTopKOp, (QueryOperator *) orderPo);
	switchSubtrees((QueryOperator *) fscoreTopKOp, (QueryOperator *) orderPo);

	AttributeReference *orderByAr = getAttrRefByName((QueryOperator *) orderPo, FSCORETOPK);
	OrderExpr *ordExpr = createOrderExpr((Node *) orderByAr, SORT_DESC, SORT_NULLS_LAST);
	OrderOperator *fscoreTopKOrderBy = createOrderOp(singleton(ordExpr), (QueryOperator *) orderPo, NIL);

	addParent((QueryOperator *) orderPo, (QueryOperator *) fscoreTopKOrderBy);
	switchSubtrees((QueryOperator *) orderPo, (QueryOperator *) fscoreTopKOrderBy);


	// add LIMIT top-k
	int k = INT_VALUE((Constant *) topk);

	//TODO: postgresql specific
	LimitOperator *fscoreTopKOrderByLimit =
			createLimitOp((Node *) createConstInt(k), NULL, (QueryOperator *) fscoreTopKOrderBy, NIL);

	addParent((QueryOperator *) fscoreTopKOrderBy, (QueryOperator *) fscoreTopKOrderByLimit);
	switchSubtrees((QueryOperator *) fscoreTopKOrderBy, (QueryOperator *) fscoreTopKOrderByLimit);

	INFO_OP_LOG("Top-k patterns that are ordered: ", fscoreTopKOrderByLimit);

	// add a projection to wrap LIMIT
	List *lExprs = NIL;
	int lPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, lPos, 0, a->dataType);
		lExprs = appendToTailOfList(lExprs, ar);

		lPos++;
	}

	ProjectionOperator *limitPo = createProjectionOp(lExprs,
			(QueryOperator *) fscoreTopKOrderByLimit, NIL, getAttrNames(fscoreTopKOrderByLimit->op.schema));

	addParent((QueryOperator *) fscoreTopKOrderByLimit, (QueryOperator *) limitPo);
	switchSubtrees((QueryOperator *) fscoreTopKOrderByLimit, (QueryOperator *) limitPo);


	//this needs to be parents of topKPattOnlyConst
	//creating fscoreTopKOnlyCons

	//fscoreTopKOnlyConst
	ProjectionOperator *fscoreTopKOnlyConsOp = createProjectionOp(topKattr,
			(QueryOperator *) topKPattOnlyConst, NIL, topKattrNames);

	addParent((QueryOperator *) topKPattOnlyConst, (QueryOperator *) fscoreTopKOnlyConsOp);
	switchSubtrees((QueryOperator *) topKPattOnlyConst, (QueryOperator *) fscoreTopKOnlyConsOp);

	// add projection for order by
	List *ocoExprs = NIL;
	int ocoPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOnlyConsOp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, ocoPos, 0, a->dataType);
		ocoExprs = appendToTailOfList(ocoExprs, ar);

		ocoPos++;
	}

	ProjectionOperator *OcOrderPo = createProjectionOp(ocoExprs,
			(QueryOperator *) fscoreTopKOnlyConsOp, NIL, getAttrNames(fscoreTopKOnlyConsOp->op.schema));

	addParent((QueryOperator *) fscoreTopKOnlyConsOp, (QueryOperator *) OcOrderPo);
	switchSubtrees((QueryOperator *) fscoreTopKOnlyConsOp, (QueryOperator *) OcOrderPo);


	//order by fscoreTopKOnlyConst
	AttributeReference *orderByArOnlyCons = getAttrRefByName((QueryOperator *) OcOrderPo, FSCORETOPK);
	OrderExpr *ordExprOnlyCons = createOrderExpr((Node *) orderByArOnlyCons, SORT_DESC, SORT_NULLS_LAST);
	OrderOperator *fscoreTopKOnlyConsOrderBy =
			createOrderOp(singleton(ordExprOnlyCons), (QueryOperator *) OcOrderPo, NIL);

	addParent((QueryOperator *) OcOrderPo, (QueryOperator *) fscoreTopKOnlyConsOrderBy);
	switchSubtrees((QueryOperator *) OcOrderPo, (QueryOperator *) fscoreTopKOnlyConsOrderBy);

	INFO_OP_LOG("Top-k patterns containing only constants with fscore: ", fscoreTopKOnlyConsOrderBy);


	//creating fscoreTopKOnlyConstSamp
	//creating SELECT MIN(fscoreTopK) FROM fscoreTopK
	//this needs to be parents of fscoreTopK(orderByOp)
	List *minExpr = NIL;
	List *minName = NIL;
	QueryOperator *mQo = (QueryOperator *) copyObject(limitPo);

//	AttributeReference *minAr = createFullAttrReference(FSCORETOPK, 0, topKpos, 0, DT_STRING);
	AttributeReference *minAr = getAttrRefByName((QueryOperator *) limitPo, FSCORETOPK);

	FunctionCall *minf = createFunctionCall("MIN", singleton(minAr));
	minf->isAgg = TRUE;

	minExpr = appendToTailOfList(minExpr, minf);
	minName = appendToTailOfList(minName, MINFSCORETOPK);

//	ProjectionOperator *minfscore = createProjectionOp(minExpr, mQo, NIL, minName);
	AggregationOperator *minfscore = createAggregationOp(minExpr, NIL, mQo, NIL, minName);
	addParent(mQo, (QueryOperator *) minfscore);

	// TODO: make min function attribute float
	FOREACH(AttributeDef, n, minfscore->op.schema->attrDefs)
		n->dataType = DT_FLOAT;


	//creating fscoreTopK > (SELECT MIN(fscoreTopK) FROM fscoreTopK)
	//creating fscoreTopKOnlyConstSamp
	//this needs to be parents of fscoreTopKOnlyConst

	// add an additional projection
	List *projExprs = NIL;
	int arPos = 0;

	FOREACH(AttributeDef, a, minfscore->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, arPos, 0, a->dataType);
		projExprs = appendToTailOfList(projExprs, ar);

		arPos++;
	}

	ProjectionOperator *minfscorePO = createProjectionOp(projExprs,
			(QueryOperator *) minfscore, NIL, getAttrNames(minfscore->op.schema));

	addParent((QueryOperator *) minfscore, (QueryOperator *) minfscorePO);
	switchSubtrees((QueryOperator *) minfscore, (QueryOperator *) minfscorePO);


	// create cross product
	List *inputs = LIST_MAKE(fscoreTopKOnlyConsOrderBy, minfscorePO);
	List *attrNames = CONCAT_LISTS(getAttrNames(fscoreTopKOnlyConsOrderBy->op.schema), singleton(MINFSCORETOPK));

	// create selection comparison min fscore with fscore of patterns with only constants
	// make minfscoretopk from right-side of the join

	QueryOperator *cp = (QueryOperator *) createJoinOp(JOIN_CROSS, NULL, inputs, NIL, attrNames);
	makeAttrNamesUnique((QueryOperator *) cp);

	addParent((QueryOperator *) fscoreTopKOnlyConsOrderBy, (QueryOperator *) cp);
	addParent((QueryOperator *) minfscorePO, (QueryOperator *) cp);

	switchSubtrees((QueryOperator *) fscoreTopKOnlyConsOrderBy, (QueryOperator *) cp);


	// create selection comparison min fscore with fscore of patterns with only constants
	AttributeReference *fscoreTopKar = getAttrRefByName((QueryOperator *) cp, FSCORETOPK);
	AttributeReference *minFscoreTopK =  getAttrRefByName((QueryOperator *) cp, MINFSCORETOPK);
	Node *minCond = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(fscoreTopKar, minFscoreTopK));
	SelectionOperator *gtmin = createSelectionOp(minCond, (QueryOperator *) cp, NIL, getAttrNames(cp->schema));

	addParent((QueryOperator *) cp, (QueryOperator *) gtmin);
	switchSubtrees((QueryOperator *) cp, (QueryOperator *) gtmin);


	projExprs = NIL;
	arPos = 0;
	List *sampAttrNames = NIL;

	FOREACH(AttributeDef, a, gtmin->op.schema->attrDefs)
	{
		if(!streq(a->attrName, MINFSCORETOPK))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, arPos, 0, a->dataType);
			projExprs = appendToTailOfList(projExprs, ar);
			sampAttrNames = appendToTailOfList(sampAttrNames, a->attrName);
		}

		arPos++;
	}

	ProjectionOperator *fscoreTopKOnlyConstPo = createProjectionOp(projExprs, (QueryOperator *) gtmin, NIL, sampAttrNames);
	addParent((QueryOperator *) gtmin, (QueryOperator *) fscoreTopKOnlyConstPo);
	switchSubtrees((QueryOperator *) gtmin, (QueryOperator *) fscoreTopKOnlyConstPo);


	// add LIMIT top-k
	//TODO: postgresql specific
	LimitOperator *fscoreTopKOnlyConstSamp = createLimitOp((Node *) createConstInt(k),
			NULL, (QueryOperator *) fscoreTopKOnlyConstPo, NIL);

	addParent((QueryOperator *) fscoreTopKOnlyConstPo, (QueryOperator *) fscoreTopKOnlyConstSamp);
	switchSubtrees((QueryOperator *) fscoreTopKOnlyConstPo, (QueryOperator *) fscoreTopKOnlyConstSamp);

	INFO_OP_LOG("Top-k patterns containing only constants whose fscores are "
			"larger than minimum of fscore of top-k patterns: ", fscoreTopKOnlyConstSamp);

	// add a projection to wrap LIMIT
	lExprs = NIL;
	lPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOnlyConstSamp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, lPos, 0, a->dataType);
		lExprs = appendToTailOfList(lExprs, ar);

		lPos++;
	}

	ProjectionOperator *limitPoSamp = createProjectionOp(lExprs,
			(QueryOperator *) fscoreTopKOnlyConstSamp, NIL, getAttrNames(fscoreTopKOnlyConstSamp->op.schema));

	addParent((QueryOperator *) fscoreTopKOnlyConstSamp, (QueryOperator *) limitPoSamp);
	switchSubtrees((QueryOperator *) fscoreTopKOnlyConstSamp, (QueryOperator *) limitPoSamp);


	// UNION top-k patterns
	List *allInput = LIST_MAKE(limitPo, limitPoSamp);
	QueryOperator *unionOp = (QueryOperator *) createSetOperator(SETOP_UNION, allInput,
			NIL, getAttrNames(fscoreTopKOrderByLimit->op.schema));

	addParent((QueryOperator *) limitPo, (QueryOperator *) unionOp);
	addParent((QueryOperator *) limitPoSamp, (QueryOperator *) unionOp);

	switchSubtrees((QueryOperator *) limitPo, unionOp);

	List *JoinAttrNames = NIL;
	List *joinList = NIL;
	Node *joinCondt = NULL;

// for new unionOp is topK
	FOREACH(AttributeDef, L, unionOp->schema->attrDefs)
	{
		FOREACH(AttributeDef, R, clean->op.schema->attrDefs)
		{
			if(streq(L->attrName, R->attrName))
			{
				AttributeReference *arL = createFullAttrReference(L->attrName, 0,
							getAttrPos((QueryOperator *) unionOp, L->attrName), 0, L->dataType);
				AttributeReference *arR = createFullAttrReference(R->attrName, 1,
							getAttrPos((QueryOperator *) clean, R->attrName), 0, R->dataType);

				//creating is null expression for left side
				Node *condN = (Node *) createIsNullExpr((Node *) arL);
				//creating left and right expression for both left and right side
				Node *condEq = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(arL, arR));
				// creating the OR condition
				Node *cond = (Node *) createOpExpr(OPNAME_OR, LIST_MAKE(condN, condEq));

				joinList = appendToTailOfList(joinList, cond);
			}
		}
	}

	joinCondt = (Node *) createOpExpr(OPNAME_AND, joinList);

	QueryOperator *copyClean = copyObject(clean);
	List *allInputJoin = LIST_MAKE((QueryOperator *) unionOp, copyClean);
	JoinAttrNames = CONCAT_LISTS(getAttrNames(unionOp->schema), getAttrNames(clean->op.schema));
	QueryOperator *joinOp = (QueryOperator *) createJoinOp(JOIN_INNER, joinCondt, allInputJoin, NIL, JoinAttrNames);

	makeAttrNamesUnique((QueryOperator *) joinOp);
	SET_BOOL_STRING_PROP(joinOp, PROP_MATERIALIZE);

	addParent(copyClean, joinOp);
	addParent((QueryOperator *) unionOp, joinOp);

	switchSubtrees((QueryOperator *) unionOp, (QueryOperator *) joinOp);
	DEBUG_NODE_BEATIFY_LOG("Join Patterns with Data: ", joinOp);

	// Add projection to exclude unnecessary attributes
	List *projExprsClean = NIL;
	List *attrNamesClean = NIL;

	FOREACH(AttributeDef, a, joinOp->schema->attrDefs)
	{
		//TODO: implement the subset of the other
		char *attrRName = substr(a->attrName, 0, strlen(a->attrName) - 2);

//		if(!isSuffix(a->attrName, "1"))
		if(!searchListString(attrNamesClean, attrRName))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
				getAttrPos((QueryOperator *) joinOp, a->attrName), 0, a->dataType);

			projExprsClean = appendToTailOfList(projExprsClean,ar);
			attrNamesClean = appendToTailOfList(attrNamesClean,ar->name);
		}
	}

	ProjectionOperator *po = createProjectionOp(projExprsClean, NULL, NIL, attrNamesClean);
	addChildOperator((QueryOperator *) po, (QueryOperator *) joinOp);
	switchSubtrees((QueryOperator *) joinOp, (QueryOperator *) po);
	SET_BOOL_STRING_PROP(po, PROP_MATERIALIZE);

	// Adding duplicate elimination
	projExprsClean = NIL;
	List *attrDefs = po->op.schema->attrDefs;

	FOREACH(AttributeDef, a, attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0,
			getAttrPos((QueryOperator *) po, a->attrName), 0, a->dataType);

		projExprsClean = appendToTailOfList(projExprsClean,ar);
	}

	QueryOperator *dr = (QueryOperator *) createDuplicateRemovalOp(projExprsClean, (QueryOperator *) po, NIL, getAttrDefNames(attrDefs));
	addParent((QueryOperator *) po,dr);
	switchSubtrees((QueryOperator *) po, (QueryOperator *) dr);
	SET_BOOL_STRING_PROP(dr, PROP_MATERIALIZE);

	//Adding CODE FOR R^2 here for testing purposes this will move after JOIN/ get data
	List *aggrsAnalysis = NIL;
	List *groupByAnalysis = NIL;
	List *analysisCorrNames = NIL;

	AttributeReference *arDist = createFullAttrReference("Total_IG", 0,
							 getAttrPos(dr, "Total_IG"), 0, DT_INT);

	FOREACH(AttributeDef, n, dr->schema->attrDefs)
	{
		if(isPrefix(n->attrName, "value"))
		{
			if(isSubstr(n->attrName, "left") != FALSE)
			{
				analysisCorrNames = appendToTailOfList(analysisCorrNames, CONCAT_STRINGS(n->attrName, "_r2"));
			}
			else if(isSubstr(n->attrName, "right") != FALSE)
			{
				analysisCorrNames = appendToTailOfList(analysisCorrNames, CONCAT_STRINGS(n->attrName, "_r2"));
			}

		}
	}

	FOREACH(AttributeDef, n, dr->schema->attrDefs)
	{
		if(isPrefix(n->attrName, "value"))
		{
			List *functioninput = NIL;
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
									 getAttrPos(dr, n->attrName), 0, n->dataType);

			functioninput = appendToTailOfList(functioninput, ar);
			functioninput = appendToTailOfList(functioninput, arDist);
			FunctionCall *r_2 = createFunctionCall("regr_r2", functioninput);
			FunctionCall *coalesce = createFunctionCall("COALESCE", LIST_MAKE(r_2, createConstInt(0)));
			Node *input = (Node *) createOpExpr("+", LIST_MAKE(createConstInt(1), coalesce));
			aggrsAnalysis = appendToTailOfList(aggrsAnalysis, input);
		}
		else if(!isPrefix(n->attrName, "Total"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
									 getAttrPos(dr, n->attrName), 0, n->dataType);
			groupByAnalysis = appendToTailOfList(groupByAnalysis, ar);
			analysisCorrNames = appendToTailOfList(analysisCorrNames, n->attrName);
		}
	}

	AggregationOperator *analysisAggr = createAggregationOp(aggrsAnalysis, groupByAnalysis, NULL, NIL, analysisCorrNames);
	addChildOperator((QueryOperator *) analysisAggr, (QueryOperator *) dr);
	switchSubtrees((QueryOperator *) dr, (QueryOperator *) analysisAggr);


	LOG_RESULT("Rewritten Pattern Generation tree for patterns", analysisAggr);
	return analysisAggr;

}


static QueryOperator *
rewriteIG_Analysis (AggregationOperator *patterns)
{
	List *projExprs = NIL;
	List *projNames = NIL;
	List *meanr2Exprs = NIL;
	int pos = 0;

	//getting original attributes back
	FOREACH(AttributeDef, n, patterns->op.schema->attrDefs)
	{
		if(isSuffix(n->attrName, "r2"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								pos, 0, n->dataType);
			projExprs = appendToTailOfList(projExprs, ar);
			meanr2Exprs = appendToTailOfList(meanr2Exprs, ar);
			projNames = appendToTailOfList(projNames, n->attrName);
			pos = pos + 1;
		}
	}

	FOREACH(AttributeDef, n, patterns->op.schema->attrDefs)
	{
		if(!isSuffix(n->attrName, "r2"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								pos, 0, n->dataType);
			projExprs = appendToTailOfList(projExprs, ar);
			projNames = appendToTailOfList(projNames, n->attrName);
			pos = pos + 1;
		}
	}

	int l = LIST_LENGTH(meanr2Exprs);
	Node *meanr2 = (Node *) (createOpExpr("/", LIST_MAKE(createOpExpr("+", meanr2Exprs), createConstInt(l))));
	projExprs = appendToTailOfList(projExprs, meanr2);
	projNames = appendToTailOfList(projNames, "mean_r2");

	ProjectionOperator *analysis = createProjectionOp(projExprs, NULL, NIL, projNames);
	addChildOperator((QueryOperator *) analysis, (QueryOperator *) patterns);
	switchSubtrees((QueryOperator *) patterns, (QueryOperator *) analysis);


	List *fscoreExprs = NIL;
	List *fscoreNames = NIL;
	List *sumExprs = NIL;
	List *prodExprs = NIL;

	FOREACH(AttributeDef, n, analysis->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
							getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);

		fscoreExprs = appendToTailOfList(fscoreExprs, ar);
		fscoreNames = appendToTailOfList(fscoreNames, n->attrName);
	}

	FOREACH(AttributeDef, n, analysis->op.schema->attrDefs)
	{
		if(streq(n->attrName, "pattern_IG"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			prodExprs = appendToTailOfList(prodExprs, ar);
		}

		if(streq(n->attrName, "coverage"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			prodExprs = appendToTailOfList(prodExprs, ar);
		}

		if(streq(n->attrName, "informativeness"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			prodExprs = appendToTailOfList(prodExprs, ar);
		}

		if(streq(n->attrName, "mean_r2"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			prodExprs = appendToTailOfList(prodExprs, ar);
		}
	}

	int fCount = LIST_LENGTH(prodExprs);
	prodExprs = appendToTailOfList(prodExprs, createConstInt(fCount));
	Node *prod = (Node *) (createOpExpr("*", prodExprs));
	Node *sumOp = (Node *) (createOpExpr("+", sumExprs));

	Node *f_score = (Node *) (createOpExpr("/", LIST_MAKE(prod, sumOp)));

	fscoreExprs = appendToTailOfList(fscoreExprs, f_score);
	fscoreNames = appendToTailOfList(fscoreNames, FSCORE);

	QueryOperator *fscore = (QueryOperator *) createProjectionOp(fscoreExprs, NULL, NIL, fscoreNames);
	addChildOperator((QueryOperator *) fscore, (QueryOperator *) analysis);
	switchSubtrees((QueryOperator *) analysis, (QueryOperator *) fscore);

	// add projection for ORDER BY
	pos = 0;
	List *projExpr = NIL;

	FOREACH(AttributeDef,a,fscore->schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(strdup(a->attrName), 0, pos, 0, a->dataType);

		if(streq(a->attrName,FSCORE))
			f_score = (Node *) ar;

		projExpr = appendToTailOfList(projExpr, ar);
		pos++;
	}

	ProjectionOperator *projForOrder = createProjectionOp(projExpr, NULL, NIL, getAttrNames(fscore->schema));
	addChildOperator((QueryOperator *) projForOrder, (QueryOperator *) fscore);
	switchSubtrees((QueryOperator *) fscore, (QueryOperator *) projForOrder);

	// add order by clause
	Node *ordCond = f_score;
	OrderExpr *ordExpr = createOrderExpr(ordCond, SORT_DESC, SORT_NULLS_LAST);
	OrderOperator *ord = createOrderOp(singleton(ordExpr), (QueryOperator *) projForOrder, NIL);

	addParent((QueryOperator *) projForOrder, (QueryOperator *) ord);
	switchSubtrees((QueryOperator *) projForOrder, (QueryOperator *) ord);


	//new limit goes here
	//another limit after union to make sure we have correct amount of patterns
	int k = INT_VALUE((Constant *) topk);

	LimitOperator *lo =
			createLimitOp((Node *) createConstInt(k), NULL, (QueryOperator *) ord, NIL);

	addParent((QueryOperator *) ord, (QueryOperator *) lo);
	switchSubtrees((QueryOperator *) ord, (QueryOperator *) lo);

	INFO_OP_LOG("Top-k patterns that are ordered: ", lo);

	// add a projection to wrap LIMIT
	List *lExprs = NIL;
	int lpos = 0;

	FOREACH(AttributeDef, a, ord->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, lpos, 0, a->dataType);
		lExprs = appendToTailOfList(lExprs, ar);

		lpos++;
	}

	ProjectionOperator *lpo = createProjectionOp(lExprs,
			(QueryOperator *) lo, NIL, getAttrNames(lo->op.schema));

	addParent((QueryOperator *) lo, (QueryOperator *) lpo);
	switchSubtrees((QueryOperator *) lo, (QueryOperator *) lpo);

	return (QueryOperator *) lpo;

}

static QueryOperator *
rewriteIG_Projection (ProjectionOperator *op)
{
    ASSERT(OP_LCHILD(op));
    DEBUG_LOG("REWRITE-IG - Integration");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    // store original attributes in the input query
    List *origAttrs = op->projExprs;

    // store the join query
    if(HAS_STRING_PROP(OP_LCHILD(op), PROP_JOIN_OP_IG))
	{
		SET_STRING_PROP(OP_LCHILD(op), PROP_JOIN_OP_IG,
				copyObject(GET_STRING_PROP(OP_LCHILD(op), PROP_JOIN_OP_IG)));
	}
    else
    {
    	SET_STRING_PROP(op, PROP_JOIN_OP_IG, OP_LCHILD(op));
    }


    // temporary expression list to grab the case when from the input
    List *grabCaseExprs = NIL;

	// temporary expression list to grab the case when from the input
    int x = 0;
	FOREACH(AttributeReference, a, op->projExprs)
	{
		if(isA(a, CaseExpr))
		{
			grabCaseExprs = appendToTailOfList(grabCaseExprs, a);
		}
		else
		{
			x++;
		}

	}

	List *asNames = NIL;
	int y = 0;
	FOREACH(AttributeDef, a, op->op.schema->attrDefs)
	{
		if(x != y)
		{
			y ++;
		}
		else
		{
			asNames = appendToTailOfList(asNames, CONCAT_STRINGS(a->attrName, "_case"));
		}
	}

    //setting input query as string property
    SET_STRING_PROP(OP_LCHILD(op), IG_INPUT_PROP, op->projExprs);
    SET_STRING_PROP(OP_LCHILD(op), IG_INPUT_DEFS_PROP, op->op.schema->attrDefs);

    QueryOperator *child = OP_LCHILD(op);
    rewriteIG_Operator(child);

    // LEFT TABLE ATTRIBUTES 0
    // IG_L_PROP
    // RIGHT TABLE ATTRIBUTES 1
    // IG_R_PROP

    //This is FOR TESTING porposes. It helps a lot. DO NOT DELETE FOR NOW!
    //--------------------------------------------
//    List *retProjName = NIL;
//    List *retPorjExpr = NIL;
//    FOREACH(AttributeDef, n, child->schema->attrDefs)
//    {
//    	retProjName = appendToTailOfList(retProjName, n->attrName);
//    	retPorjExpr = appendToTailOfList(retPorjExpr,
//    			createFullAttrReference(n->attrName, 0,
//				getAttrPos((QueryOperator *) child, n->attrName), 0, n->dataType));
//    }
//
//    ProjectionOperator *newProj = createProjectionOp(retPorjExpr, NULL, NIL, retProjName);
//	addChildOperator((QueryOperator *) newProj, (QueryOperator *) child);
//	switchSubtrees((QueryOperator *) op, (QueryOperator *) newProj);
//
//    INFO_OP_LOG("Rewritten Projection Operator ----------", (QueryOperator *) newProj);
//    return (QueryOperator *) newProj;
    //--------------------------------------------

	// Getting Table name and length of table name here
	char *tblNameL = "";
	HashMap *attrLNames = NEW_MAP(Constant, Node);
	HashMap *attrRNames = NEW_MAP(Constant, Node);

    List *joinCond = (List *) GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING);
    List *joinAttrs = NIL;

    FOREACH(Operator, o, joinCond)
    {
    	FOREACH(AttributeReference, ar, o->args)
		{
    		joinAttrs = appendToTailOfList(joinAttrs, ar->name);
		}
    }

    FOREACH(AttributeDef, n, attrL)
	{
		if(isPrefix(n->attrName, IG_PREFIX))
		{
			int len1 = strlen(n->attrName);
			int len2 = strlen(strrchr(n->attrName, '_'));
			int len = len1 - len2 - 1;
			tblNameL = substr(n->attrName, 8, len);
			tblNameL = CONCAT_STRINGS(tblNameL, "_");
			break;
		}

		MAP_ADD_STRING_KEY(attrLNames, n->attrName, n);
	}

	char *tblNameR = "";
	FOREACH(AttributeDef, n, attrR)
	{
		if(isPrefix(n->attrName, IG_PREFIX))
		{
			int len1 = strlen(n->attrName);
			int len2 = strlen(strrchr(n->attrName, '_'));
			int len = len1 - len2 - 1;
			tblNameR = substr(n->attrName, 8, len);
			tblNameR = CONCAT_STRINGS(tblNameR, "_");
			break;
		}

		MAP_ADD_STRING_KEY(attrRNames, n->attrName, n);
	}

	List *newProjExpr = NIL;
	List *newAttrNames = NIL;
	HashMap *igAttrs = NEW_MAP(Constant, Node);

    // add ig attributes
	FOREACH(Node, n, op->projExprs)
	{
		if(isA(n, CaseExpr))
		{
			CaseExpr *ce = (CaseExpr *) n;

			FOREACH(CaseWhen, cw, ce->whenClauses)
			{
				// when condition
				List *whenArgs = ((Operator *) cw->when)->args;
				FOREACH(Node, n, whenArgs)
				{
					if(isA(n, Operator))
					{
						Operator *op = (Operator *) n;
						FOREACH(Node, arg, op->args)
						{
							// this works and changes position for maqi1
							if(isA(arg, AttributeReference))
							{
								AttributeReference *ar = (AttributeReference *) arg;
								ar->attrPosition = getAttrPos((QueryOperator *) child, ar->name);
							}

							// this works and changes the position for gdays
							if(isA(arg, IsNullExpr))
							{
								// this gets the IsNullExpr of node x and stores it in isN
								IsNullExpr *isN = (IsNullExpr *) arg;
								// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
								Node *ofisN = isN->expr;
								// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
								AttributeReference *arofisN = (AttributeReference *) ofisN;
								arofisN->attrPosition = getAttrPos((QueryOperator *) child, arofisN->name);
							}
						}
					}

					if(isA(n, AttributeReference))
					{
						FOREACH(AttributeReference, ar, whenArgs)
						{
							ar->attrPosition = getAttrPos((QueryOperator *) child,ar->name);
						}
					}
				}

				// then
				AttributeReference *then = (AttributeReference *) cw->then;
				then->attrPosition = getAttrPos((QueryOperator *) child, then->name);
			}

			// else
			AttributeReference *els = (AttributeReference *) ce->elseRes;
			els->attrPosition = getAttrPos((QueryOperator *) child, els->name);

			newProjExpr = appendToTailOfList(newProjExpr, n);
		}
		else
		{
			AttributeReference *a = (AttributeReference *) n;
			AttributeReference *ar = createFullAttrReference(a->name, 0,
			    				getAttrPos((QueryOperator *) child, a->name), 0, a->attrType);

			newProjExpr = appendToTailOfList(newProjExpr, ar);
		}
	}

	// add case when statement that merge common attribute value
	List *newProjExprWithCaseWhen = NIL;

	FOREACH(Node, n, newProjExpr)
	{
		if(!isA(n, CaseExpr) && !isA(n, Operator))
		{
			AttributeReference *ar = (AttributeReference *) n;
			if(MAP_HAS_STRING_KEY(attrLNames, ar->name) &&
					MAP_HAS_STRING_KEY(attrRNames, ar->name))
			{
				//TODO: find the partner attribute
				char *attrName = CONCAT_STRINGS(ar->name,"1");
				AttributeReference *arr = NULL;

				if(isA((Node *) child, SelectionOperator))
				{
					QueryOperator *grandChild = OP_LCHILD(child);
					arr = createFullAttrReference(attrName, 0,
							getAttrPos((QueryOperator *) grandChild, attrName), 0, ar->attrType);
				}
				else
					arr = getAttrRefByName((QueryOperator *) child, attrName);

				// common value
				Node *cond = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(ar,arr));
				Node *then = (Node *) ar;
				CaseWhen *caseWhen1 = createCaseWhen(cond, then);

				// leftside null
				cond = (Node *) createIsNullExpr((Node *) ar);
				then = (Node *) arr;
				CaseWhen *caseWhen2 = createCaseWhen(cond, then);

				// rightside null
				cond = (Node *) createIsNullExpr((Node *) arr);
				then = (Node *) ar;
				CaseWhen *caseWhen3 = createCaseWhen(cond, then);

				// both null
				cond = (Node *)createOpExpr(OPNAME_AND,
						LIST_MAKE(createIsNullExpr((Node *) ar),createIsNullExpr((Node *) arr)));

				if(ar->attrType == DT_STRING || ar->attrType == DT_VARCHAR2)
					then = (Node *) createConstString("na");
				if(ar->attrType == DT_INT || ar->attrType == DT_FLOAT || ar->attrType == DT_LONG)
					then = (Node *) createConstInt(0);

				CaseWhen *caseWhen4 = createCaseWhen(cond, then);

				Node *els = (Node *) ar;
				CaseExpr *caseExpr = createCaseExpr(NULL, LIST_MAKE(caseWhen1,caseWhen2,caseWhen3,caseWhen4), els);
				newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, caseExpr);
			}
			else
			{
				AttributeReference *ar = (AttributeReference *) n;
				FunctionCall *coalesce = NULL;

				if(ar->attrType == DT_STRING || ar->attrType == DT_VARCHAR2)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstString("na")));

				if(ar->attrType == DT_INT || ar->attrType == DT_FLOAT || ar->attrType == DT_LONG)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstInt(99999)));

				newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, (Node *) coalesce);
			}
		}
		else
		{
			FunctionCall *coalesce = NULL;
			if(isA(n,CaseExpr))
			{
				CaseExpr *ce = (CaseExpr *) n;
				AttributeReference *els = (AttributeReference *) ce->elseRes;

				if(els->attrType == DT_STRING || els->attrType == DT_VARCHAR2)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstString("na")));

				if(els->attrType == DT_INT || els->attrType == DT_FLOAT || els->attrType == DT_LONG)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstInt(99999)));
			}
			else
			{
				FATAL_LOG("!! Under Construction !!");
			}

			newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, (Node *) coalesce);
		}
	}


	FOREACH(AttributeDef, a, op->op.schema->attrDefs)
		newAttrNames = appendToTailOfList(newAttrNames, a->attrName);

    FOREACH(AttributeDef, a, child->schema->attrDefs)
    {
    	if(a->dataType == DT_BIT10)
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0,
    				getAttrPos((QueryOperator *) child, a->attrName), 0, a->dataType);

    		newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, ar);
    		newAttrNames = appendToTailOfList(newAttrNames, ar->name);

    		MAP_ADD_STRING_KEY(igAttrs, ar->name, ar);
    	}
    }

    // collect join columns
    List *commonAttrNames = NIL;
    List *commonAttrNamesR = NIL;
    List *joinAttrNames = NIL;
    List *joinAttrNamesR = NIL;

    // add additional ig columns
    List *addIgExprs = NIL;
    List *addIgAttrs = NIL;

    List *allAttrLR = CONCAT_LISTS(copyObject(attrL), copyObject(attrR));

    FOREACH(AttributeDef, a, allAttrLR)
    {
    	if(!isPrefix(a->attrName,IG_PREFIX) && !isSuffix(a->attrName,"_anno"))
    	{
            if(MAP_HAS_STRING_KEY(attrLNames, a->attrName) &&
            		MAP_HAS_STRING_KEY(attrRNames, a->attrName))
        	{
            	char *igName = CONCAT_STRINGS("ig_conv_",
    //        			MAP_HAS_STRING_KEY(attrLNames, a->attrName) ? tblNameL : tblNameR,
            			MAP_HAS_STRING_KEY(attrLNames, a->attrName) ? "left_" : "right_",
            					a->attrName);

    			char *igNameR = CONCAT_STRINGS("ig_conv_",
//						MAP_HAS_STRING_KEY(attrLNames, a->attrName) ? tblNameR : tblNameL,
    					MAP_HAS_STRING_KEY(attrRNames, a->attrName) ? "right_" : "left_",
								a->attrName);

    			//TODO: no need to store them as constant
//    			Constant *constIgName = createConstString(igName);
//				Constant *constIgNameR = createConstString(igNameR);

    			// store join attributes as IG attributes
    			AttributeDef *adlIg = (AttributeDef *) copyObject(MAP_GET_STRING(attrLNames, a->attrName));
    			adlIg->attrName = igName;
    			adlIg->dataType = DT_BIT10;

    			AttributeDef *adrIg = (AttributeDef *) copyObject(MAP_GET_STRING(attrRNames, a->attrName));
    			adrIg->attrName = igNameR;
    			adrIg->dataType = DT_BIT10;

            	if(!searchListString(joinAttrs, a->attrName))
        		{
        			if(!searchListNode(commonAttrNames, (Node *) adlIg))
        				commonAttrNames = appendToTailOfList(commonAttrNames, adlIg);

        			if(!searchListNode(commonAttrNamesR, (Node *) adrIg))
            			commonAttrNamesR = appendToTailOfList(commonAttrNamesR, adrIg);
        		}
        		else
        		{
        			if(!searchListNode(joinAttrNames, (Node *) adlIg))
        				joinAttrNames = appendToTailOfList(joinAttrNames, adlIg);

					if(!searchListNode(joinAttrNamesR, (Node *) adrIg))
            			joinAttrNamesR = appendToTailOfList(joinAttrNamesR, adrIg);
        		}
        	}
    	}
    }

    // adding ig attribute after the integration
    FOREACH(Node, n, op->projExprs)
    {
    	if(!isA(n, CaseExpr))
    	{
    		AttributeReference *ar = (AttributeReference *) n;

    		//TODO: remove unique number in the attr from shared
    		char *origAttrName = ar->name;

    		char *igName = CONCAT_STRINGS("ig_conv_",
    									MAP_HAS_STRING_KEY(attrLNames, origAttrName) ? tblNameL : tblNameR, origAttrName);

    		char *attrNameAfterReplace = replaceSubstr(ar->name,gprom_itoa(1),"");
    		igName = replaceSubstr(igName, origAttrName, attrNameAfterReplace);

    		if(MAP_HAS_STRING_KEY(igAttrs, igName))
    		{
    			AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
    			AttributeReference *ar = createFullAttrReference(igExpr->name, 0, igExpr->attrPosition, 0, igExpr->attrType);

    			addIgExprs = appendToTailOfList(addIgExprs, ar);
    			addIgAttrs = appendToTailOfList(addIgAttrs, CONCAT_STRINGS(igName,INTEG_SUFFIX));
    		}

    	}

    	if(isA(n, CaseExpr))
    	{
    		CaseExpr *ce = copyObject((CaseExpr *) n);
    		Node *el = ce->elseRes;
    		AttributeReference *ar = NULL;
    		char *igName = NULL;

    		//TODO: then can be an expression.
			FOREACH(CaseWhen, cw, ce->whenClauses)
			{

				ar = (AttributeReference *) cw->then;
				igName = CONCAT_STRINGS("ig_conv_", MAP_HAS_STRING_KEY(attrLNames, ar->name) ? tblNameL : tblNameR, ar->name);

				if(MAP_HAS_STRING_KEY(igAttrs, igName))
				{
					AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
					cw->then = (Node *) igExpr;
				}
			}

			//TODO: else can be an expression.
			ar = (AttributeReference *) el;
			char *origAttrName = ar->name;

			igName = CONCAT_STRINGS("ig_conv_",
										MAP_HAS_STRING_KEY(attrLNames, origAttrName) ? tblNameL : tblNameR,
												origAttrName);

    		char *attrNameAfterReplace = replaceSubstr(ar->name,gprom_itoa(1),"");
    		igName = replaceSubstr(igName, origAttrName, attrNameAfterReplace);

			if(MAP_HAS_STRING_KEY(igAttrs, igName))
			{
				AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
				ce->elseRes = (Node *) igExpr;
			}

			addIgExprs = appendToTailOfList(addIgExprs, ce);
			addIgAttrs = appendToTailOfList(addIgAttrs, CONCAT_STRINGS(igName,INTEG_SUFFIX));
    	}
    }


    List *allExprs = CONCAT_LISTS(newProjExprWithCaseWhen,addIgExprs);
    List *allAttrs = CONCAT_LISTS(newAttrNames,addIgAttrs);

	ProjectionOperator *newProj1 = createProjectionOp(allExprs, NULL, NIL, allAttrs);
    addChildOperator((QueryOperator *) newProj1, (QueryOperator *) child);
    switchSubtrees((QueryOperator *) op, (QueryOperator *) newProj1);

    // TODO: ig columns should be binary
    FOREACH(AttributeDef, ad, newProj1->op.schema->attrDefs)
    {
    	if(isPrefix(ad->attrName,IG_PREFIX) && isSuffix(ad->attrName,INTEG_SUFFIX))
    	{
    		ad->dataType = DT_BIT10;
    	}
    }

    // TODO: coalesce becomes DT_STRING
    int pos = 0;
    List *newProjExprs = NIL;

    FOREACH(Node, n, newProj1->projExprs)
    {
    	if(isA(n,FunctionCall))
    	{
    		// change the datatype in attrDef to original datatype
    		AttributeDef *a = getAttrDefByPos((QueryOperator *) newProj1,pos);
    		QueryOperator *child = (QueryOperator *) getHeadOfListP(newProj1->op.inputs);
    		AttributeDef *childa = getAttrDefByName(child,a->attrName);
    		a->dataType = childa->dataType;

    		// apply cast to coalesce
			CastExpr *cast = createCastExpr(n, childa->dataType);
			newProjExprs = appendToTailOfList(newProjExprs, cast);
    	}
    	else
    	{
        	newProjExprs = appendToTailOfList(newProjExprs, n);
    	}

    	pos++;
    }

    newProj1->projExprs = newProjExprs;

    // if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
    if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
    {
        SET_STRING_PROP(newProj1, PROP_JOIN_ATTRS_FOR_HAMMING,
                copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
    }

    //add property for common attributes
    SET_STRING_PROP(newProj1, IG_PROP_JOIN_ATTR, joinAttrNames);
    SET_STRING_PROP(newProj1, IG_PROP_JOIN_ATTR_R, joinAttrNamesR);

    SET_STRING_PROP(newProj1, IG_PROP_NON_JOIN_COMMON_ATTR, commonAttrNames);
    SET_STRING_PROP(newProj1, IG_PROP_NON_JOIN_COMMON_ATTR_R, commonAttrNamesR);

    //origAttrs gets declared in line 1925
    SET_STRING_PROP(newProj1, IG_PROP_ORIG_ATTR, origAttrs);

    // store the join query
	SET_STRING_PROP(newProj1, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(op, PROP_JOIN_OP_IG)));


    INFO_OP_LOG("Rewritten Operator tree for all IG attributes", newProj1);

//  This function creates hash maps and adds hamming distance functions
	ProjectionOperator *hammingvalue_op = rewriteIG_HammingFunctions(newProj1);
//	This function adds the + expression to calculate the total distance
	ProjectionOperator *sumrows = rewriteIG_SumExprs(hammingvalue_op);

	if(explFlag == FALSE)
	{

		//clean up for projection
		List *cleanExprs = NIL;
		List *cleanNames = NIL;

		//converting name : value to IG
		FOREACH(AttributeReference, a, sumrows->projExprs)
		{
			if(!isA(a, Operator))
			{
				if(isPrefix(a->name, VALUE_IG))
				{
					char *displayName = NULL;
					cleanExprs = appendToTailOfList(cleanExprs, a);
					char *s2 = substr(a->name, 6, strlen(a->name) - 1); //contains : _tableName_attributeName
					displayName = CONCAT_STRINGS("IG_", s2);
					cleanNames = appendToTailOfList(cleanNames, displayName);

				}

				else
				{
					cleanExprs = appendToTailOfList(cleanExprs, a);
					cleanNames = appendToTailOfList(cleanNames, a->name);
				}
			}
		}

		FOREACH(AttributeReference, a, sumrows->projExprs)
		{
			if(isA(a, Operator))
			{
				cleanExprs = appendToTailOfList(cleanExprs, a);
				cleanNames = appendToTailOfList(cleanNames, strdup(TOTAL_IG));

			}
		}

		ProjectionOperator *cleanProj = createProjectionOp(cleanExprs, NULL, NIL, cleanNames);
		addChildOperator((QueryOperator *) cleanProj, (QueryOperator *) sumrows);
		switchSubtrees((QueryOperator *) sumrows, (QueryOperator *) cleanProj);

		INFO_OP_LOG("Rewritten Operator tree for patterns", (QueryOperator *) sumrows);
		return (QueryOperator *) cleanProj;
	}
	else
	{
		AggregationOperator *patterns = rewriteIG_PatternGeneration(sumrows);
		QueryOperator *analysis = rewriteIG_Analysis(patterns);
		INFO_OP_LOG("Rewritten Operator tree for patterns", (QueryOperator *) analysis);

		//this was only created for QueryOperator *analysis
		//do not use it with AggregationOperator
		QueryOperator *cleanqo = cleanEXPL((QueryOperator *) analysis);

		return cleanqo;
	}
}

static QueryOperator *
rewriteIG_Join (JoinOperator *op)
{
    DEBUG_LOG("REWRITE-IG - Join");

    QueryOperator *lChild = OP_LCHILD(op);
    QueryOperator *rChild = OP_RCHILD(op);

    int LeftLen = LIST_LENGTH(lChild->schema->attrDefs);
//  int RightLen = LIST_LENGTH(rChild->schema->attrDefs);

	SET_STRING_PROP(lChild, IG_INPUT_PROP,
			copyObject(GET_STRING_PROP(op, IG_INPUT_PROP)));

	SET_STRING_PROP(rChild, IG_INPUT_PROP,
			copyObject(GET_STRING_PROP(op, IG_INPUT_PROP)));

	List *projDefsProp = (List *) GET_STRING_PROP(op, IG_INPUT_DEFS_PROP);
	SET_STRING_PROP(lChild, IG_INPUT_DEFS_PROP, projDefsProp);
	SET_STRING_PROP(rChild, IG_INPUT_DEFS_PROP, projDefsProp);

	List *lProp = copyObject(lChild->schema->attrDefs);
	List *rProp = copyObject(rChild->schema->attrDefs);
	List *joinExprs = getAttrReferences((Node *) op);

//	Sending IG join type in IG_JOIN_TYPE to table access
//	AttributeReference *jt = NULL;
	Constant *joinType = NULL;
	if(op->joinType == JOIN_INNER)
	{
//		jt = createFullAttrReference("INNER_JOIN", 0, 0, 0, DT_STRING);
		joinType = createConstString("INNER_JOIN");
	}
	else if(op->joinType == JOIN_CROSS)
	{
//		jt = createFullAttrReference("CROSS_JOIN", 0, 0, 0, DT_STRING);
		joinType = createConstString("CROSS_JOIN");
	}
	else if(op->joinType == JOIN_LEFT_OUTER)
	{
//		jt = createFullAttrReference("LEFT_OUTER_JOIN", 0, 0, 0, DT_STRING);
		joinType = createConstString("LEFT_OUTER_JOIN");
	}
	else if(op->joinType == JOIN_RIGHT_OUTER)
	{
//		jt = createFullAttrReference("RIGHT_OUTER_JOIN", 0, 0, 0, DT_STRING);
		joinType = createConstString("RIGHT_OUTER_JOIN");
	}
	else if(op->joinType == JOIN_FULL_OUTER)
	{
//		jt = createFullAttrReference("FULL_OUTER_JOIN", 0, 0, 0, DT_STRING);
		joinType = createConstString("FULL_OUTER_JOIN");
	}

//	SET_STRING_PROP(lChild, IG_JOIN_TYPE, jt);
//	SET_STRING_PROP(rChild, IG_JOIN_TYPE, jt);

	SET_STRING_PROP(lChild, IG_JOIN_TYPE, joinType);
	SET_STRING_PROP(rChild, IG_JOIN_TYPE, joinType);

	SET_STRING_PROP(lChild, IG_JOIN_PROP, joinExprs);
	SET_STRING_PROP(rChild, IG_JOIN_PROP, joinExprs);

	// sending property up the tree to selection op and projection
	SET_STRING_PROP(op, IG_L_PROP, lProp);
	SET_STRING_PROP(op, IG_R_PROP, rProp);

	// sending property down the tree to table access op
	SET_STRING_PROP(lChild, IG_L_PROP, lProp);
	SET_STRING_PROP(rChild, IG_L_PROP, lProp);
	SET_STRING_PROP(lChild, IG_R_PROP, rProp);
	SET_STRING_PROP(rChild, IG_R_PROP, rProp);


	// FOR SINGLE WHERE CLAUSE
	if(HAS_STRING_PROP(op, PROP_WHERE_CLAUSE))
	{
		Node *cond = GET_STRING_PROP(op, PROP_WHERE_CLAUSE);
		Operator *condOp = (Operator *) cond;
		List *arList = condOp->args; // should only be 2 conditions for now simple cases only
		int listLen = LIST_LENGTH(arList);
		if(listLen == 2) // if 1 ar and 1 constant
		{
			FOREACH(AttributeReference, ar, arList)
			{
				if(isA(ar, AttributeReference))
				{
					if(ar->attrPosition > LeftLen)
					{
						SET_STRING_PROP(rChild, PROP_WHERE_CLAUSE,
								copyObject(GET_STRING_PROP(op, PROP_WHERE_CLAUSE)));
					}
					else if(ar->attrPosition >= LeftLen)
					{
						SET_STRING_PROP(lChild, PROP_WHERE_CLAUSE,
								copyObject(GET_STRING_PROP(op, PROP_WHERE_CLAUSE)));
					}
				}
			}
		}
	}

	// FOR AND OR / MULTIPLE WHERE CLAUSES
	int countL = 0;
	int countR = 0;

	//if they are from the same table then entire property needs to go in
	if(HAS_STRING_PROP(op, PROP_WHERE_CLAUSE))
	{
		Node *cond = GET_STRING_PROP(op, PROP_WHERE_CLAUSE);
		Operator *condOp = (Operator *) cond;
		List *arList = condOp->args; // should only be 2 conditions for now simple cases only
		if(streq(condOp->name, "AND")) // if the op name is AND
		{
			FOREACH(Operator, o, arList)
			{
				List *args = o->args;
				FOREACH(Node, n, args)
				{
					if(isA(n, AttributeReference))
					{
						AttributeReference *ar = (AttributeReference *) n;
						if(ar->attrPosition < LeftLen)
						{
							countL = countL + 1;
						}
						else if(ar->attrPosition >= LeftLen)
						{
							countR = countR + 1;
						}
					}
				}
			}
		}
	}

	//TODO: dealing with more than two conditions
	if(countL == 2)
	{
		SET_STRING_PROP(lChild, PROP_WHERE_CLAUSE,
				copyObject(GET_STRING_PROP(op, PROP_WHERE_CLAUSE)));
	}
	else if(countR == 2)
	{
		SET_STRING_PROP(rChild, PROP_WHERE_CLAUSE,
				copyObject(GET_STRING_PROP(op, PROP_WHERE_CLAUSE)));
	}
	else
	{
		// sending correct properties for both tables for AND, OR : this works if both attribute references
		// are in different tables
		if(HAS_STRING_PROP(op, PROP_WHERE_CLAUSE))
		{
			Node *cond = GET_STRING_PROP(op, PROP_WHERE_CLAUSE);
			Operator *condOp = (Operator *) cond;
			List *arList = condOp->args; // should only be 2 conditions for now simple cases only

			if(streq(condOp->name, "AND")) // if the op name is AND
			{
				FOREACH(Operator, o, arList)
				{
					List *args = o->args;
					FOREACH(Node, n, args)
					{
						if(isA(n, AttributeReference))
						{
							AttributeReference *ar = (AttributeReference *) n;
							if(ar->attrPosition < LeftLen)
							{
								SET_STRING_PROP(lChild, PROP_WHERE_CLAUSE, o);
							}
							else if(ar->attrPosition >= LeftLen)
							{
								SET_STRING_PROP(rChild, PROP_WHERE_CLAUSE, o);
							}
						}
					}
				}
			}
			else if(streq(condOp->name, "OR")) // if the op name is AND
			{
				FOREACH(Operator, o, arList)
				{
					List *args = o->args;
					FOREACH(Node, n, args)
					{
						if(isA(n, AttributeReference))
						{
							AttributeReference *ar = (AttributeReference *) n;
							if(ar->attrPosition < LeftLen)
							{
								SET_STRING_PROP(lChild, PROP_WHERE_CLAUSE, o);
							}
						}
					}
				}
			}
		}
	}

	lChild = rewriteIG_Operator(lChild);
	rChild = rewriteIG_Operator(rChild);


	// update the attribute def for join operator
    List *lAttrDefs = copyObject(getNormalAttrs(lChild));
    List *rAttrDefs = copyObject(getNormalAttrs(rChild));

    attrL = copyObject(lAttrDefs);
    attrR = copyObject(rAttrDefs);


    List *newAttrDefs = CONCAT_LISTS(lAttrDefs,rAttrDefs);
    op->op.schema->attrDefs = copyObject(newAttrDefs);

    makeAttrNamesUnique((QueryOperator *) op);

    List *attrLists = ((Operator *) op->cond)->args;
    List *attrNames = NIL;
    boolean isSingle = FALSE;

    FOREACH(Node, n, attrLists)
    	if(isA(n, AttributeReference))
    		isSingle = TRUE;

    if(isSingle)
    	SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING, singleton(op->cond));
    else
    {
        FOREACH(Node, n, attrLists) {
         	attrNames = appendToTailOfList(attrNames, n);
        }

        SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING, attrNames);
    }


	LOG_RESULT("Rewritten Join Operator tree",op);
    return (QueryOperator *) op;
}

static QueryOperator *
rewriteIG_TableAccess(TableAccessOperator *op)
{

	int relAccessCount = getRelNameCount(&nameState, op->tableName);

	DEBUG_LOG("REWRITE-IG - Table Access <%s> <%u>", op->tableName, relAccessCount);

	// copy any as of clause if there
	if (asOf)
		op->asOf = copyObject(asOf);

	//creating input for conversion
	List *inputL = NIL; // owned
	List *inputR = NIL; // shared
	List *inputName = NIL;
	List *input_attrs = (List *) GET_STRING_PROP((QueryOperator *) op, IG_INPUT_PROP);
	List *input_defs = (List *) GET_STRING_PROP((QueryOperator *) op, IG_INPUT_DEFS_PROP);
	List *joinattrs = (List *) GET_STRING_PROP((QueryOperator *) op, IG_JOIN_PROP);
	List *left_attrs = (List *) GET_STRING_PROP((QueryOperator *) op, IG_L_PROP);
	List *right_attrs = (List *) GET_STRING_PROP((QueryOperator *) op, IG_R_PROP);
//	AttributeReference *joinType = (AttributeReference *) GET_STRING_PROP((QueryOperator *) op, IG_JOIN_TYPE);
	Constant *joinType = (Constant *) GET_STRING_PROP((QueryOperator *) op, IG_JOIN_TYPE);

    FOREACH(AttributeReference, ar, input_attrs)
    {
    	if(isSuffix(ar->name,"1"))
    	{
    		ar->name = replaceSubstr(ar->name,"1","");
    	}
    }

	int left_len = LIST_LENGTH(left_attrs);
//	int right_len = LIST_LENGTH(right_attrs);

	// adding input attributes
	FOREACH(AttributeReference, ar, input_attrs) // loop for all attrRef in properties
	{
		if(ar->attrPosition < left_len) // creating left list
		{
			if(isA(ar, AttributeReference))
			{
				inputL = appendToTailOfList(inputL, ar);
				inputName = appendToTailOfList(inputName, ar->name);
			}
		}
		else if(ar->attrPosition >= left_len)
		{
			if(isA(ar, AttributeReference))
			{
				inputR = appendToTailOfList(inputR, ar);
				inputName = appendToTailOfList(inputName, ar->name);
			}
		}
	}

	//adding the s.maqi to left side if it exist in owned table
	FOREACH(AttributeDef, adef, op->op.schema->attrDefs)
	{
		if(searchArList(inputL, adef->attrName) == 0)
		{
			if(searchArList(inputR, adef->attrName) == 1)
			{
				AttributeReference *ar = createFullAttrReference(adef->attrName, 0,
						getAttrPos((QueryOperator *) op, adef->attrName), 0, adef->dataType);
				inputL = appendToTailOfList(inputL, ar);
				inputName = appendToTailOfList(inputName, adef->attrName);
			}
		}
	}

	//getting inputs from case when expression
	List *caseWhenAttrs = NIL;
	List *thenElseAttrs = NIL;
	FOREACH(AttributeReference, ar, input_attrs)
	{
		if(isA(ar, CaseExpr))
		{
			CaseExpr *ce = (CaseExpr *) ar;
			FOREACH(CaseWhen, cw, ce->whenClauses)
			{
				// when condition
				List *whenArgs = ((Operator *) cw->when)->args;
				FOREACH(Node, n, whenArgs)
				{
					if(isA(n, Operator))
					{
						Operator *nop = (Operator *) n;
						FOREACH(Node, arg, nop->args)
						{
							if(isA(arg, AttributeReference))
							{
								AttributeReference *ar = (AttributeReference *) arg;
								caseWhenAttrs = appendToTailOfList(caseWhenAttrs, ar);
							}

							if(isA(arg, IsNullExpr))
							{
								// this gets the IsNullExpr of node x and stores it in isN
								IsNullExpr *isN = (IsNullExpr *) arg;
								// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
								Node *ofisN = isN->expr;
								// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
								AttributeReference *arofisN = (AttributeReference *) ofisN;
								caseWhenAttrs = appendToTailOfList(caseWhenAttrs, arofisN);
							}
						}
					}
				}

				// then
				AttributeReference *then = (AttributeReference *) cw->then;
				caseWhenAttrs = appendToTailOfList(caseWhenAttrs, then);
				thenElseAttrs = appendToTailOfList(thenElseAttrs, then);
			}

			// else
			AttributeReference *els = (AttributeReference *) ce->elseRes;
			caseWhenAttrs = appendToTailOfList(caseWhenAttrs, els);
			thenElseAttrs = appendToTailOfList(thenElseAttrs, els);
		}
	}

	FOREACH(AttributeReference, ar , thenElseAttrs)
	{
    	if(isSuffix(ar->name,"1"))
    	{
    		ar->name = replaceSubstr(ar->name,"1","");
    	}
	}

	int pos = searchCasePosinArList(input_attrs);

	if(pos != -1)
	{
		int i = 0;
		AttributeDef *caseDef = NULL;
		FOREACH(AttributeDef, adef, input_defs)
		{
			if(i != pos)
			{
				i = i + 1;
			}
			else if(i == pos)
			{
				caseDef = adef;
				break;
			}
		}

		//adding case when attribute(dayswaqi) for Q2 to its proper place here
		FOREACH(AttributeDef, adef, left_attrs)
		{
			// if found in left list
			if(strcmp(adef->attrName, caseDef->attrName) == 0) // if they are same
			{
				inputL = appendToTailOfList(inputL,
							createFullAttrReference(caseDef->attrName, 0,
							getAttrPos((QueryOperator *) op, caseDef->attrName), 0, caseDef->dataType));
				break;
			}
		}

		FOREACH(AttributeDef, adef, right_attrs)
		{
			// if found in left list
			if(strcmp(adef->attrName, caseDef->attrName) == 0) // if they are same
			{
				inputR = appendToTailOfList(inputR,
							createFullAttrReference(caseDef->attrName, 0,
							getAttrPos((QueryOperator *) op, caseDef->attrName), 0, caseDef->dataType));
				break;
			}
		}
	}


	// removing duplicates here
	List *cleanL = NIL;
	List *cleanR = NIL;

	FOREACH(AttributeReference, ar, inputL)
	{
		if(cleanL == NIL)
		{
			cleanL = appendToTailOfList(cleanL, ar);
		}
		else if(searchArList(cleanL, ar->name) == 0)
		{
			cleanL = appendToTailOfList(cleanL, ar);
		}
		else
		{
			continue;
		}
	}

	FOREACH(AttributeReference, ar, inputR)
	{
		if(cleanR == NIL)
		{
			cleanR = appendToTailOfList(cleanR, ar);
		}
		else if(searchArList(cleanR, ar->name) == 0)
		{
			cleanR = appendToTailOfList(cleanR, ar);
		}
		else
		{
			continue;
		}
	}

	List *attrNames = NIL;
	List *projExpr = NIL;

	//normal attributes for the current table
	FOREACH(AttributeDef, attr, op->op.schema->attrDefs)
	{
		attrNames = appendToTailOfList(attrNames, strdup(attr->attrName));
		projExpr = appendToTailOfList(projExpr, createFullAttrReference(attr->attrName, 0,
				getAttrPos((QueryOperator *) op, attr->attrName), 0, attr->dataType));
	}

	ProjectionOperator *inputPo = createProjectionOp(projExpr, NULL, NIL, attrNames);

	//cleanL and cleanR contains input query attributes without duplicates
	//removing those attributes from projExpr so i can duplicate them to create ig_ attributes
	List *newProjExpr = NIL;
	List *newProjNames = NIL;
	if(tablePos == 0)
	{
		newProjExpr = NIL;
		newProjNames = NIL;
		FOREACH(AttributeReference, ar, cleanL)
		{
			//removing the join condition attributes
//			if(searchArList(joinattrs, ar->name) == 1)
//			{
//				continue;
//			}
//			//removing the attributes from left list that do not exist in the right list
//			else if(searchArList(cleanR, ar->name) == 0)
//			{
//				continue;
//			}
//			else
			if((searchArList(joinattrs, ar->name) == 0)
					&& (searchArList(cleanR, ar->name) == 1))
//			if((!searchListNode(joinattrs, (Node *) ar))
//					&& (searchListNode(cleanR, (Node *) ar)))
			{
				newProjExpr = appendToTailOfList(newProjExpr, ar);
				newProjNames = appendToTailOfList(newProjNames, ar->name);
			}
		}

		//adding case attributes to input here, NOTE: We only need then and else attributes here
		FOREACH(AttributeReference, ar , thenElseAttrs)
		{
			if(ar->attrPosition < left_len) // creating left list
			{
				newProjExpr = appendToTailOfList(newProjExpr, ar);
				newProjNames = appendToTailOfList(newProjNames, ar->name);
			}
		}
	}
	else if(tablePos == 1)
	{
		newProjExpr = NIL;
		newProjNames = NIL;
		FOREACH(AttributeReference, ar, cleanR)
		{
			//removing the join condition attributes
			if(searchArList(joinattrs, ar->name) == 1)
			{
				continue;
			}
			else
			{
				newProjExpr = appendToTailOfList(newProjExpr, ar);
				newProjNames = appendToTailOfList(newProjNames, ar->name);
			}
		}

		//adding case attributes to input here, NOTE: We only need then and else attributes here
		FOREACH(AttributeReference, ar , thenElseAttrs)
		{
			if(ar->attrPosition >= left_len)
			{
				newProjExpr = appendToTailOfList(newProjExpr, ar);
				newProjNames = appendToTailOfList(newProjNames, ar->name);
			}
		}
	}

	// Creating IG attributes
    char *newAttrName = NULL;
    List *copyAllattrs = copyObject(newProjExpr);

    //TODO: retrieve the original attribute name
    FOREACH(AttributeReference, ar, copyAllattrs)
    {
    	if(isSuffix(ar->name,"1"))
    	{
    		ar->name = replaceSubstr(ar->name,"1","");
    	}
    }

	// duplicating IG attributes
    if(tablePos == 0)
    {
        FOREACH(AttributeDef, attr, inputPo->op.schema->attrDefs)
        {
        	//check an attribute is an attribute in the projection operation of input query
        	if(searchArList(copyAllattrs, attr->attrName) == 1)
        	{
            	newAttrName = getIgAttrName("left", attr->attrName, relAccessCount);
            	attrNames = appendToTailOfList(attrNames, newAttrName);
            	projExpr = appendToTailOfList(projExpr, createFullAttrReference(attr->attrName, 0,
            					getAttrPos((QueryOperator *) op, attr->attrName), 0, attr->dataType));
        	}
        }
    }

    if(tablePos == 1)
    {
        FOREACH(AttributeDef, attr, inputPo->op.schema->attrDefs)
        {
        	//check an attribute is an attribute in the projection operation of input query
        	if(searchArList(copyAllattrs, attr->attrName) == 1)
        	{
            	newAttrName = getIgAttrName("right", attr->attrName, relAccessCount);
            	attrNames = appendToTailOfList(attrNames, newAttrName);
            	projExpr = appendToTailOfList(projExpr, createFullAttrReference(attr->attrName, 0,
            					getAttrPos((QueryOperator *) op, attr->attrName), 0, attr->dataType));
        	}

        }
    }

    //removing duplicates from joinattrs to be added again FOR FULL OUTER JOIN AND RIGHT OUTER JOIN
    List *joinattrs1 = NIL;
	FOREACH(AttributeReference, ar, joinattrs)
	{
		if(joinattrs1 == NIL)
		{
			joinattrs1 = appendToTailOfList(joinattrs1, ar);
		}
		else if(searchArList(joinattrs1, ar->name) == 0)
		{
			joinattrs1 = appendToTailOfList(joinattrs1, ar);
		}
		else
		{
			continue;
		}
	}

	//cleanL and cleanR have the input query attributes
	// adding the join attributes if its a FULL OUTER JOIN OR RIGHT OUTER JOIN
	if((streq(STRING_VALUE(joinType), "FULL_OUTER_JOIN")) ||
			(streq(STRING_VALUE(joinType), "RIGHT_OUTER_JOIN")))
	{
		FOREACH(AttributeReference, ar, joinattrs1)
		{
			if(tablePos == 0) // if owned
			{
				if(searchArList(cleanR, ar->name) == 1 &&
						searchArList(cleanL, ar->name) == 1) // if the join attribute exists in right input
				{
					// duplicating that attribute
					projExpr = appendToTailOfList(projExpr, createFullAttrReference(ar->name, 0,
								getAttrPos((QueryOperator *) op, ar->name), 0, ar->attrType));
					char *name = getIgAttrName("left", ar->name, relAccessCount);
					attrNames = appendToTailOfList(attrNames, name);
				}
			}

			if(tablePos == 1) // if shared
			{
				if(searchArList(cleanR, ar->name) == 1)
				{
					projExpr = appendToTailOfList(projExpr, createFullAttrReference(ar->name, 0,
								getAttrPos((QueryOperator *) op, ar->name), 0, ar->attrType));
					char *name = getIgAttrName("right", ar->name, relAccessCount);
					attrNames = appendToTailOfList(attrNames, name);
				}
			}
		}
	}

	ProjectionOperator *po = createProjectionOp(projExpr, NULL, NIL, attrNames);
	SET_BOOL_STRING_PROP((QueryOperator *) po, PROP_PROJ_IG_ATTR_DUP);

	if(HAS_STRING_PROP(op, PROP_WHERE_CLAUSE))
	{
		Node *selCond = GET_STRING_PROP(op, PROP_WHERE_CLAUSE);
		List *argsOp = (List *) ((Operator *) selCond)->args;

		if(isA(selCond, Operator))
		{
			if((streq(((Operator *) selCond)->name,"AND")) ||
					(streq(((Operator *) selCond)->name,"OR")))
			{
				FOREACH(Operator, o, argsOp)
				{
					FOREACH(AttributeReference, ar, o->args)
					{
						if(isA(ar, AttributeReference))
						{
							if(isSuffix(ar->name,"1"))
							{
								ar->name = replaceSubstr(ar->name,"1","");
							}
							ar->attrPosition = searchArListForPos(po->projExprs, ar->name);
							break;
						}
					}
				}
			}
			else
			{
				FOREACH(AttributeReference, ar, argsOp)
				{
					if(isSuffix(ar->name,"1"))
					{
						ar->name = replaceSubstr(ar->name,"1","");
					}
					ar->attrPosition = searchArListForPos(po->projExprs, ar->name);
					break;
				}
			}

			List *whereNames = NIL;
			FOREACH(AttributeDef, adef, op->op.schema->attrDefs)
			{
				whereNames = appendToTailOfList(whereNames, adef->attrName);
			}

			//adding where clause i.e selection operator
			SelectionOperator *so = createSelectionOp(selCond, NULL, NIL, whereNames);
			so->op.schema->attrDefs = op->op.schema->attrDefs;

			addChildOperator((QueryOperator *) so, (QueryOperator *) op);
			// Switch the subtree with this newly created projection operator.
			switchSubtrees((QueryOperator *) op, (QueryOperator *) so);

			addChildOperator((QueryOperator *) po, (QueryOperator *) so);
			// Switch the subtree with this newly created projection operator.
			switchSubtrees((QueryOperator *) so, (QueryOperator *) po);

		}
	}
	else
	{
		addChildOperator((QueryOperator *) po, (QueryOperator *) op);
		// Switch the subtree with this newly created projection operator.
	    switchSubtrees((QueryOperator *) op, (QueryOperator *) po);
	}

    tablePos = tablePos + 1; // to change 0 from 1
    DEBUG_LOG("table access after adding additional attributes for ig: %s", operatorToOverviewString((Node *) po));
    return rewriteIG_Conversion(po);
}

