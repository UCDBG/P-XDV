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
#define INTEG_SUFFIX "_integ"
#define IG_RIGHT "right_"
#define IG_LEFT "left_"
#define ANNO_SUFFIX "_anno"
#define HAMMING_PREFIX "hamming_"
#define IG_WHERE_ATTRS_PROP "IG_WHERE_ATTRS_PROP"
#define PATTERN_IG "pattern_IG"
#define TOTAL_IG "Total_IG"
#define COVERAGE "coverage"
#define INFORMATIVENESS "informativeness"
#define FSCORETOPK "fscoreTopK"

// explanations
#define MATCH_COUNT "match_count"
#define AVG_PRICE "avg_p"
#define GLOBAL_AVG_PRICE "global_avg_p"
#define PRICE_RATIO "price_ratio"
#define RELATIVE_PCT "relative_pct"
#define DISCOUNT_PCT "discount_pct"
#define EXPLANATION_TEXT "explanation"

static boolean igIsConvertedOutputAttr(char *attrName);
//pricing
#define PRICE_PREFIX "price_"
#define TOTAL_PRICE "Total_Price"
#define DEFAULT_TUPLE_PRICE 100

static ProjectionOperator *rewriteIG_Pricing(ProjectionOperator *cleanProj);
static ProjectionOperator *rewriteIG_RoundFinalNumericOutput(ProjectionOperator *priceProj);
static Node *igMakeFloatConstInt(int v);
static Node *igMakeSumOrSingle(List *exprs);
static Node *igGetPostedPriceExpr(ProjectionOperator *cleanProj);
static int igGetPricingScopeSize(List *igRefs);
static boolean igFinalIGMatchesSellerAttr(char *igName, char *sellerAttrName);

//pricing
static Node *igRound2(Node *expr);
static boolean igIsPostedPriceAttr(char *attrName);

static AttributeReference *igGetDirectProjectedAttr(Node *expr);

/*
 * Find an existing converted IG helper without reconstructing its name.
 * GProM escapes underscores in generated helper names (e.g.,
 * delay_status -> delay__status), so rebuilding names from SQL identifiers
 * is unsafe.
 */
static AttributeReference *igFindConvertedAttr(
        QueryOperator *op,
        char *baseName,
        boolean rightSide);

static QueryOperator *rewriteIG_Operator (QueryOperator *op);
static QueryOperator *rewriteIG_Conversion (ProjectionOperator *op);
static QueryOperator *rewriteIG_Projection(ProjectionOperator *op);
static QueryOperator *rewriteIG_Selection(SelectionOperator *op);
static QueryOperator *rewriteIG_Join(JoinOperator *op);
static QueryOperator *rewriteIG_TableAccess(TableAccessOperator *op);
static QueryOperator *rewriteIG_Limit(LimitOperator *op);
static ProjectionOperator *rewriteIG_SumExprs(ProjectionOperator *op);
static ProjectionOperator *rewriteIG_HammingFunctions(ProjectionOperator *op);

static void igSyncProjectionTypesWithChild(ProjectionOperator *po);
static void igSyncProjectionRefsWithChild(ProjectionOperator *po);
static List *igCollectWhereAttrsForSide(
        Node *cond,
        QueryOperator *child,
        int sideOffset,
        int sideLen);
static void igRefreshExprRefsAgainstChild(
        Node *expr,
        QueryOperator *child);
static void igNormalizeJoinCondRefsBySide(
        JoinOperator *op,
        QueryOperator *lChild,
        QueryOperator *rChild);

static QueryOperator *
rewriteIG_PatternExplanations(QueryOperator *patterns);

static AttributeReference *igGetAttrRefAny(
        QueryOperator *op,
        char *name1,
        char *name2);

static Node *igConcatText(List *parts);
static Node *igText(Node *expr);
static Node *igSafeDivide(Node *numerator, Node *denominator);
static Node *igWhenPresent(AttributeReference *ar, Node *text);

static Node *igOwnerChangeText(
        AttributeReference *integrated,
        AttributeReference *owner,
        char *attrName);


static Node *asOf;
static RelCount *nameState;
List *attrL = NIL;
List *attrR = NIL;
static List *igJoinAttrNames = NIL;

int tablePos = 0;

static boolean explFlag;
static boolean igFlag;
static Node *topk;

QueryOperator *
rewriteIG (ProvenanceComputation  *op)
{
    START_TIMER("rewrite - IG rewrite");

    // unset relation name counters
    nameState = (RelCount *) NULL;
    igJoinAttrNames = NIL;

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
        case T_LimitOperator:
            rewrittenOp = rewriteIG_Limit((LimitOperator *) op);
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


/*
 * Rewrite an existing SQL LIMIT operator.
 *
 * LimitOperator / T_LimitOperator are already part of GProM.  The parser has
 * already created the LIMIT node (including its limitExpr / offsetExpr), so
 * this function does not construct a new LIMIT.  It only rewrites the child
 * and refreshes the LIMIT schema to match the rewritten child.
 *
 * This keeps the implementation consistent with the other P-XDV rewrite
 * helpers such as rewriteIG_Join(), rewriteIG_Projection(), etc.
 */
static QueryOperator *
rewriteIG_Limit(LimitOperator *op)
{
    ASSERT(OP_LCHILD((QueryOperator *) op));

    /*
     * For an ordinary IG OF query:
     *
     *     Limit
     *       Projection
     *         Selection
     *           Join
     *
     * rewrite the subtree under LIMIT and preserve this existing LIMIT node.
     */
    QueryOperator *child = OP_LCHILD((QueryOperator *) op);

    rewriteIG_Operator(child);

    /*
     * Lower rewrite stages may replace the original child subtree with the
     * final P-XDV projection via switchSubtrees(), so fetch the current child
     * again after rewriting.
     */
    child = OP_LCHILD((QueryOperator *) op);

    /*
     * LIMIT is schema preserving.  The LIMIT output AttributeDefs therefore
     * have to match the final rewritten child exactly.
     */
    op->op.schema->attrDefs = copyObject(child->schema->attrDefs);

    /*
     * A SQL LIMIT inside the input query of IGEXPL has different semantics
     * from IGEXPL TOP k.  IGEXPL TOP k already creates its own LimitOperator
     * later, after ranking patterns.  Until input-LIMIT semantics are placed
     * explicitly before pattern generation, reject this combination instead
     * of silently limiting the wrong stage.
     */
    if(explFlag)
    {
        FATAL_LOG(
                "LIMIT inside the input query of IGEXPL is not supported yet");
        return NULL;
    }

    INFO_OP_LOG("Rewritten LIMIT operator", op);

    return (QueryOperator *) op;
}


/*
 * Collect every source attribute referenced anywhere in a WHERE predicate for
 * one side of a join.
 *
 * The Selection condition uses positions in the combined join schema:
 *
 *     [ left attributes | right attributes ]
 *
 * We map those positions back to the real child schema and create fresh,
 * side-local AttributeReferences.  This avoids all previous assumptions about
 * "one condition", exactly two AND terms, or manually walking only one/two
 * levels of the predicate tree.
 *
 * getAttrReferences() recursively visits nested operators, so predicates such
 * as
 *
 *     (a.x > 1 AND (b.y = 2 OR b.z IS NULL)) AND b.w < 10
 *
 * are handled uniformly.
 */
static List *
igCollectWhereAttrsForSide(
        Node *cond,
        QueryOperator *child,
        int sideOffset,
        int sideLen)
{
    List *result = NIL;

    if(cond == NULL || child == NULL || sideLen <= 0)
        return result;

    List *refs = getAttrReferences(cond);

    FOREACH(AttributeReference, ar, refs)
    {
        int combinedPos = ar->attrPosition;

        if(combinedPos < sideOffset
                || combinedPos >= sideOffset + sideLen)
            continue;

        int localPos = combinedPos - sideOffset;
        AttributeDef *childDef = getAttrDefByPos(child, localPos);

        if(childDef == NULL)
            continue;

        if(searchArList(result, childDef->attrName) == 0)
        {
            result = appendToTailOfList(
                    result,
                    createFullAttrReference(
                            childDef->attrName,
                            0,
                            localPos,
                            0,
                            childDef->dataType));
        }
    }

    return result;
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


    /*
     * Update every AttributeReference in the original Selection condition
     * recursively after the child rewrite.  The old code walked at most two
     * levels and therefore missed nested WHERE predicates.
     */
    List *selectionRefs = getAttrReferences(op->cond);

    FOREACH(AttributeReference, ar, selectionRefs)
    {
        int attrPos = getAttrPos(child, ar->name);

        if(attrPos >= 0)
        {
            AttributeDef *childDef = getAttrDefByPos(child, attrPos);
            ar->attrPosition = attrPos;

            if(childDef != NULL)
                ar->attrType = childDef->dataType;
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


/*
 * Keep ProjectionOperator expression metadata and output schema metadata in
 * sync with the actual child schema.
 *
 * GProM validates both:
 *   (1) AttributeReference::attrType in projExprs, and
 *   (2) AttributeDef::dataType in the projection schema.
 *
 * During the old bit(10) -> int8 transition, some generated AttributeReference
 * objects and some projection AttributeDefs could retain DT_BIT10 even though
 * the child column had already become DT_LONG.  That produces:
 *
 *   attribute datatype and child attrdef datatypes are not the same
 *
 * This helper repairs both sides from the actual child schema.
 */
static void
igSyncProjectionTypesWithChild(ProjectionOperator *po)
{
    if(po == NULL || OP_LCHILD(po) == NULL)
        return;

    QueryOperator *child = OP_LCHILD(po);
    int childLen = LIST_LENGTH(child->schema->attrDefs);
    int outPos = 0;

    FOREACH(Node, expr, po->projExprs)
    {
        /*
         * getAttrReferences() returns the AttributeReference nodes contained
         * in the expression, including references nested inside CASE, CAST,
         * function calls, and operators.
         */
        List *refs = getAttrReferences(expr);

        FOREACH(AttributeReference, ar, refs)
        {
            AttributeDef *childDef = NULL;

            /*
             * Projection expressions normally reference the single child by
             * position.  Position is preferred because generated aliases may
             * intentionally differ from the child's internal escaped name.
             */
            if(ar->attrPosition >= 0 && ar->attrPosition < childLen)
                childDef = getAttrDefByPos(child, ar->attrPosition);

            /*
             * Fallback to name lookup if the position is unavailable.
             */
            if(childDef == NULL
                    && ar->name != NULL
                    && getAttrPos(child, ar->name) >= 0)
                childDef = getAttrDefByName(child, ar->name);

            if(childDef != NULL)
                ar->attrType = childDef->dataType;
        }

        /*
         * The converted IG helpers are now int8 end-to-end.  Their output
         * AttributeDefs must agree with the rewritten expressions as well.
         */
        AttributeDef *outDef = getAttrDefByPos((QueryOperator *) po, outPos);

        if(outDef != NULL
                && (isPrefix(outDef->attrName, IG_PREFIX)
                    || isPrefix(outDef->attrName, HAMMING_PREFIX)))
            outDef->dataType = DT_LONG;

        outPos++;
    }
}

/*
 * Synchronize AttributeReferences in a projection expression with the
 * projection's current child schema. GProM checks both the reference name
 * and attrPosition against the child AttributeDef at that position.
 *
 * For projections constructed by this cleanup, attrPosition is authoritative.
 * Output aliases are intentionally left untouched; only references to the
 * child are normalized.
 */
static void
igSyncProjectionRefsWithChild(ProjectionOperator *po)
{
    if(po == NULL || OP_LCHILD(po) == NULL)
        return;

    QueryOperator *child = OP_LCHILD(po);
    int childLen = LIST_LENGTH(child->schema->attrDefs);

    FOREACH(Node, expr, po->projExprs)
    {
        List *refs = getAttrReferences(expr);

        FOREACH(AttributeReference, ar, refs)
        {
            AttributeDef *childDef = NULL;

            if(ar->attrPosition >= 0 && ar->attrPosition < childLen)
            {
                childDef = getAttrDefByPos(child, ar->attrPosition);
            }
            else if(ar->name != NULL)
            {
                int childPos = getAttrPos(child, ar->name);

                if(childPos >= 0)
                {
                    ar->attrPosition = childPos;
                    childDef = getAttrDefByPos(child, childPos);
                }
            }

            if(childDef != NULL)
            {
                if(ar->name == NULL || !streq(ar->name, childDef->attrName))
                    ar->name = strdup(childDef->attrName);

                ar->attrType = childDef->dataType;
            }
        }
    }
}

//rewriteIG_Conversion
static QueryOperator *
rewriteIG_Conversion (ProjectionOperator *op)
{
    /*
     * Fast path for numeric-only conversion.
     *
     * Table-access rewriting has already created the ig_conv_* helper
     * columns.  The previous numeric path added a second materialized
     * projection only to cast those helpers to int8, followed by the final
     * schema/order/alias boundary.
     *
     * Put the casts directly in that final boundary instead:
     *
     *      helper projection
     *          -> final cast/order/alias boundary
     *
     * This removes one generated SQL/CTE layer per numeric input.
     *
     * String helpers do not use this path because they still require the
     * established ASCII/UNNEST/aggregation pipeline.
     */
    boolean needsAsciiConversion = FALSE;

    FOREACH(AttributeDef, a, op->op.schema->attrDefs)
    {
        if(isPrefix(a->attrName, IG_PREFIX)
                && a->dataType == DT_STRING)
        {
            needsAsciiConversion = TRUE;
            break;
        }
    }

    if(!needsAsciiConversion)
    {
        List *fastExprs = NIL;
        List *fastNames = NIL;
        int pos = 0;

        FOREACH(AttributeDef, a, op->op.schema->attrDefs)
        {
            AttributeReference *ar =
                    createFullAttrReference(
                            a->attrName,
                            0,
                            pos,
                            0,
                            a->dataType);

            Node *expr = (Node *) ar;

            if(isPrefix(a->attrName, IG_PREFIX)
                    && a->dataType != DT_LONG)
            {
                expr =
                        (Node *) createCastExpr(
                                (Node *) ar,
                                DT_LONG);
            }

            fastExprs =
                    appendToTailOfList(
                            fastExprs,
                            expr);

            fastNames =
                    appendToTailOfList(
                            fastNames,
                            strdup(a->attrName));

            pos++;
        }

        ProjectionOperator *addPo =
                createProjectionOp(
                        fastExprs,
                        NULL,
                        NIL,
                        fastNames);

        addChildOperator(
                (QueryOperator *) addPo,
                (QueryOperator *) op);

        switchSubtrees(
                (QueryOperator *) op,
                (QueryOperator *) addPo);

        /*
         * Keep escaped helper spelling internal, but expose the original
         * source identifier spelling at this stable conversion boundary.
         */
        FOREACH(AttributeDef, a, addPo->op.schema->attrDefs)
        {
            if(isPrefix(a->attrName, IG_PREFIX)
                    && isSubstr(a->attrName, "__"))
            {
                a->attrName =
                        replaceSubstr(
                                a->attrName,
                                "__",
                                "_");
            }

            if(isPrefix(a->attrName, IG_PREFIX))
                a->dataType = DT_LONG;
        }

        /*
         * GProM checks AttributeReference name, position, and type against
         * the child schema.  Synchronize the references inside the cast
         * expressions without changing the output aliases.
         */
        igSyncProjectionTypesWithChild(addPo);

        LOG_RESULT("Converted Operator tree", addPo);
        return (QueryOperator *) addPo;
    }

    /*
     * ASCII/string path: preserve the proven implementation unchanged in
     * structure because its aggregation/materialization stages are required.
     */
    List *projExprs = NIL;
    List *attrNames = NIL;

    FOREACH(AttributeDef, a, op->op.schema->attrDefs)
    {
        projExprs =
                appendToTailOfList(
                        projExprs,
                        createFullAttrReference(
                                a->attrName,
                                0,
                                getAttrPos(
                                        (QueryOperator *) op,
                                        a->attrName),
                                0,
                                a->dataType));

        attrNames =
                appendToTailOfList(
                        attrNames,
                        a->attrName);
    }

    ProjectionOperator *po =
            createProjectionOp(
                    projExprs,
                    NULL,
                    NIL,
                    attrNames);

    po->projExprs = toAsciiList(po);

    addChildOperator(
            (QueryOperator *) po,
            (QueryOperator *) op);

    switchSubtrees(
            (QueryOperator *) op,
            (QueryOperator *) po);

    List *cleanExprs = NIL;
    List *cleanNames = NIL;

    FOREACH(AttributeDef, a, po->op.schema->attrDefs)
    {
        cleanExprs =
                appendToTailOfList(
                        cleanExprs,
                        createFullAttrReference(
                                a->attrName,
                                0,
                                getAttrPos(
                                        (QueryOperator *) po,
                                        a->attrName),
                                0,
                                a->dataType));

        cleanNames =
                appendToTailOfList(
                        cleanNames,
                        a->attrName);
    }

    ProjectionOperator *cleanpo =
            createProjectionOp(
                    cleanExprs,
                    NULL,
                    NIL,
                    cleanNames);

    addChildOperator(
            (QueryOperator *) cleanpo,
            (QueryOperator *) po);

    switchSubtrees(
            (QueryOperator *) po,
            (QueryOperator *) cleanpo);

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
            AttributeReference *ar =
                    (AttributeReference *) sta->expr;

            aggrNames =
                    appendToTailOfList(
                            aggrNames,
                            ar->name);
        }
        else
        {
            if(isA(n, AttributeReference))
            {
                groupBy =
                        appendToTailOfList(
                                groupBy,
                                n);

                groupByNames =
                        appendToTailOfList(
                                groupByNames,
                                n->name);
            }

            if(isA(n, CastExpr))
            {
                CastExpr *ce = (CastExpr *) n;
                AttributeReference *ar =
                        (AttributeReference *) ce->expr;

                groupBy =
                        appendToTailOfList(
                                groupBy,
                                (Node *) ar);
            }
        }
    }

    newNames = CONCAT_LISTS(aggrNames, groupByNames);
    aggrs = getAsciiAggrs(po->projExprs);

    AggregationOperator *ao =
            createAggregationOp(
                    aggrs,
                    groupBy,
                    NULL,
                    NIL,
                    newNames);

    FOREACH(AttributeDef, adef, ao->op.schema->attrDefs)
    {
        if(isPrefix(adef->attrName, "ig")
                && adef->dataType == DT_STRING)
        {
            adef->dataType = DT_INT;
        }
    }

    addChildOperator(
            (QueryOperator *) ao,
            (QueryOperator *) cleanpo);

    switchSubtrees(
            (QueryOperator *) cleanpo,
            (QueryOperator *) ao);

    projExprs = getARfromAttrDefs(ao->op.schema->attrDefs);

    ProjectionOperator *newPo =
            createProjectionOp(
                    projExprs,
                    NULL,
                    NIL,
                    newNames);

    addChildOperator(
            (QueryOperator *) newPo,
            (QueryOperator *) ao);

    switchSubtrees(
            (QueryOperator *) ao,
            (QueryOperator *) newPo);

    List *newProjExprs = NIL;

    FOREACH(AttributeReference, a, newPo->projExprs)
    {
        if(isPrefix(a->name, "ig"))
        {
            CastExpr *castInt =
                    createCastExpr(
                            (Node *) a,
                            DT_LONG);

            newProjExprs =
                    appendToTailOfList(
                            newProjExprs,
                            castInt);
        }
        else
        {
            newProjExprs =
                    appendToTailOfList(
                            newProjExprs,
                            a);
        }
    }

    newPo->projExprs = newProjExprs;

    FOREACH(AttributeDef, a, newPo->op.schema->attrDefs)
    {
        if(isPrefix(a->attrName, "ig"))
            a->dataType = DT_LONG;
    }

    projExprs =
            getARfromAttrDefswPos(
                    (QueryOperator *) newPo,
                    po->op.schema->attrDefs);

    newNames = getAttrNames(po->op.schema);

    ProjectionOperator *addPo =
            createProjectionOp(
                    projExprs,
                    NULL,
                    NIL,
                    newNames);

    addChildOperator(
            (QueryOperator *) addPo,
            (QueryOperator *) newPo);

    switchSubtrees(
            (QueryOperator *) newPo,
            (QueryOperator *) addPo);

    FOREACH(AttributeDef, a, addPo->op.schema->attrDefs)
    {
        if(isPrefix(a->attrName, IG_PREFIX)
                && isSubstr(a->attrName, "__"))
        {
            a->attrName =
                    replaceSubstr(
                            a->attrName,
                            "__",
                            "_");
        }

        if(isPrefix(a->attrName, IG_PREFIX))
            a->dataType = DT_LONG;
    }

    igSyncProjectionTypesWithChild(addPo);

    LOG_RESULT("Converted Operator tree", addPo);
    return (QueryOperator *) addPo;
}

static ProjectionOperator *
rewriteIG_SumExprs (ProjectionOperator *hamming_op)
{
    ASSERT(OP_LCHILD(hamming_op));
    DEBUG_LOG("REWRITE-IG - Computing tuple-level DG");
    DEBUG_LOG("Operator tree \n%s", nodeToString(hamming_op));

    /*
     * Native hamming_* columns are already the attribute-level DG values.
     * Give them their final public IG_* names here and compute Total_IG in
     * the same projection.
     */
    int pos = 0;
    List *dgRefsForTotal = NIL;
    List *sumExprs = NIL;
    List *sumNames = NIL;

    FOREACH(AttributeDef, a, hamming_op->op.schema->attrDefs)
    {
        AttributeReference *ar =
                createFullAttrReference(
                        a->attrName,
                        0,
                        pos,
                        0,
                        a->dataType);

        sumExprs = appendToTailOfList(sumExprs, ar);

        if(isPrefix(a->attrName, HAMMING_PREFIX))
        {
            char *displayName =
                    replaceSubstr(
                            a->attrName,
                            HAMMING_PREFIX,
                            "IG_");

            if(isSubstr(displayName, "__"))
                displayName = replaceSubstr(displayName, "__", "_");

            sumNames = appendToTailOfList(sumNames, displayName);
            dgRefsForTotal = appendToTailOfList(dgRefsForTotal, copyObject(ar));
        }
        else
        {
            sumNames = appendToTailOfList(sumNames, strdup(a->attrName));
        }

        pos++;
    }

    Node *sumExpr = NULL;
    if(dgRefsForTotal == NIL || LIST_LENGTH(dgRefsForTotal) == 0)
        sumExpr = (Node *) createCastExpr((Node *) createConstInt(0), DT_LONG);
    else
        sumExpr = igMakeSumOrSingle(dgRefsForTotal);

    sumExprs = appendToTailOfList(sumExprs, sumExpr);
    sumNames = appendToTailOfList(sumNames, strdup(TOTAL_IG));

    ProjectionOperator *sumrows = createProjectionOp(sumExprs, NULL, NIL, sumNames);
    addChildOperator((QueryOperator *) sumrows, (QueryOperator *) hamming_op);
    switchSubtrees((QueryOperator *) hamming_op, (QueryOperator *) sumrows);

    FOREACH(AttributeDef, a, sumrows->op.schema->attrDefs)
    {
        if(isPrefix(a->attrName, "IG_") || streq(a->attrName, TOTAL_IG))
            a->dataType = DT_LONG;
    }

    /*
     * Expressions still reference hamming_* on the child while output
     * AttributeDefs intentionally use public IG_* aliases.
     */
    igSyncProjectionTypesWithChild(sumrows);

    SET_STRING_PROP(sumrows, PROP_JOIN_OP_IG,
            copyObject(GET_STRING_PROP(hamming_op, PROP_JOIN_OP_IG)));

    return sumrows;
}


/*
 * Build a native PostgreSQL 64-bit Hamming-distance expression without
 * depending on the user-defined hammingxor()/hammingxorvalue() functions.
 *
 * PostgreSQL's bigint bitwise XOR operator (#) operates on the signed 64-bit
 * two's-complement representation. int8send() exposes the resulting 8 bytes,
 * and the built-in bit_count(bytea) returns the number of one bits.
 *
 * Generated SQL is equivalent to:
 *
 *     bit_count(int8send((left_value)::int8 # (right_value)::int8))
 *
 * This removes the old bit(10) truncation (0..1023 for positive values) and
 * all text conversions from the DG path.
 */
static Node *
createIGNativeHammingCount (Node *leftValue, Node *rightValue)
{
    /*
     * Conversion helpers used to be 10-bit values.  Some
     * AttributeReference objects can therefore still carry the old type
     * annotation even after the projection schema has been upgraded to
     * DT_LONG.  The model checker validates the type stored on the
     * AttributeReference inside the CAST, not only the CAST result, so
     * normalize fresh copies here before constructing the native Hamming
     * expression.
     */
    Node *leftCopy = copyObject(leftValue);
    Node *rightCopy = copyObject(rightValue);

    if(isA(leftCopy, AttributeReference))
        ((AttributeReference *) leftCopy)->attrType = DT_LONG;

    if(isA(rightCopy, AttributeReference))
        ((AttributeReference *) rightCopy)->attrType = DT_LONG;

    CastExpr *left64 = createCastExpr(leftCopy, DT_LONG);
    CastExpr *right64 = createCastExpr(rightCopy, DT_LONG);

    Node *xorExpr = (Node *) createOpExpr("#",
            LIST_MAKE((Node *) left64, (Node *) right64));

    FunctionCall *asBytes = createFunctionCall("int8send", singleton(xorExpr));
    asBytes->isDistinct = FALSE;

    FunctionCall *bitCount = createFunctionCall("bit_count",
            singleton((Node *) asBytes));
    bitCount->isDistinct = FALSE;

    return (Node *) bitCount;
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

	}

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

	}


    // create provenance columns using case when
    List *commonAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_NON_JOIN_COMMON_ATTR_R);
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
//							then = (Node *) createCastExpr((Node *) createConstInt(0), DT_LONG);
//							els = (Node *) origIgInteg;
//
//							caseWhen = createCaseWhen(cond, then);
//							caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//        				}
        			}
            		else // if the corresponding ig attribute does not exist
            		{
						cond = (Node *) createIsNullExpr((Node *) origIgInteg);
						then = (Node *) createCastExpr((Node *) createConstInt(0), DT_LONG);
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

				/*
				 * Conversion may already have wrapped this CASE branch in
				 * an int8 cast. Avoid generating ((x)::int8)::int8.
				 */
				if(!isA(then, CastExpr))
				{
					Node *castExpr =
							(Node *) createCastExpr(then, DT_LONG);
					cw->then = castExpr;
				}
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
                if((searchListNode(commonAttrNamesR, (Node *) a) ||
                        searchListNode(joinAttrNamesR, (Node *) a))
                        && MAP_HAS_STRING_KEY(nameToIgAttrOpp, igOrigNameInteg))
                {
                    /*
                     * A same-named buyer-side converted attribute really exists.
                     * Use it as the fallback value for a missing seller-side value.
                     */
                    AttributeReference *corrIgExpr =
                            (AttributeReference *) MAP_GET_STRING(
                                    nameToIgAttrOpp,
                                    igOrigNameInteg);

                    cond = (Node *) createIsNullExpr((Node *) origIgInteg);
                    then = (Node *) corrIgExpr;
                    els = (Node *) origIgInteg;

                    caseWhen = createCaseWhen(cond, then);
                    caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
                }
                else
                {
                    /*
                     * Do not assume that a schema-level common attribute has a
                     * converted counterpart.  A seller attribute can be present
                     * only because it is used in a CASE predicate while the
                     * buyer-side attribute is not part of A_new.
                     *
                     * Previously MAP_GET_STRING() could return NULL here, which
                     * produced an invalid CASE expression such as:
                     *
                     *   CASE WHEN ig_conv_right_maqi IS NULL THEN
                     *        ELSE ig_conv_right_maqi END
                     *
                     * and later crashed typeOf(NULL).  For an internal helper
                     * without an actual converted counterpart, normalize NULL to
                     * binary zero.  Whether the attribute contributes DG is
                     * decided separately by creation of its *_integ column.
                     */
                    cond = (Node *) createIsNullExpr((Node *) origIgInteg);
                    then = (Node *) createCastExpr(
                            (Node *) createConstInt(0),
                            DT_LONG);
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

    /*
     * CASE construction above may reuse AttributeReference nodes originating
     * from older helper metadata.  Normalize those references against the
     * real child schema before the model checker sees this projection.
     */
    FOREACH(AttributeDef, ad, newProj->op.schema->attrDefs)
        if(isPrefix(ad->attrName, IG_PREFIX))
            ad->dataType = DT_LONG;

    igSyncProjectionTypesWithChild(newProj);

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
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, DT_LONG);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
//    		continue;
    	}
    	else if(isSuffix(a->attrName, INTEG_SUFFIX))
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, DT_LONG);
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
		char* arRname = replaceSubstr(arR->name, INTEG_SUFFIX, "");
		Node *hammingdist = NULL;

		if(MAP_HAS_STRING_KEY(nameToIgAttrOpp, arRname))
		{
			AttributeReference *ar =
					(AttributeReference *) MAP_GET_STRING(nameToIgAttrOpp, arRname);
			AttributeReference *arL =
					getAttrRefByName((QueryOperator *) newProj, ar->name);

			hammingdist = createIGNativeHammingCount((Node *) arL, (Node *) arR);
		}
		else
		{
			/*
			 * Seller-only attributes are compared with zero. The native Hamming
			 * helper performs the int8 cast itself, so do not pre-cast here.
			 */
			hammingdist = createIGNativeHammingCount(
					(Node *) createConstInt(0), (Node *) arR);
		}

		exprs = appendToTailOfList(exprs, hammingdist);

		char *name = CONCAT_STRINGS(HAMMING_PREFIX,
				substr(arR->name, 8 , strlen(arR->name) - 1));
		atNames = appendToTailOfList(atNames, name);
	}


	//UNIQUE IG_INTEG ATTRIBUTES FROM L
	FOREACH(AttributeReference, arL, cleanigAttrL)
	{
		FOREACH(AttributeReference, arLOrig, igAttrL)
		{
			if(isSubstr(arL->name, arLOrig->name))
			{
				Node *hammingdist = createIGNativeHammingCount(
						(Node *) arLOrig, (Node *) arL);
				exprs = appendToTailOfList(exprs, hammingdist);

				char *name = CONCAT_STRINGS(HAMMING_PREFIX,
						substr(arL->name, 8 , strlen(arL->name) - 1));
				atNames = appendToTailOfList(atNames, name);
			}
		}
	}

	ProjectionOperator *hamming_op = createProjectionOp(exprs, NULL, NIL, atNames);

	FOREACH(AttributeDef, n, hamming_op->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, HAMMING_PREFIX))
		{
			n->dataType = DT_LONG;
		}
	}

	FOREACH(AttributeReference, n, hamming_op->projExprs)
	{
		if(isPrefix(n->name, HAMMING_PREFIX))
		{
			n->attrType = DT_LONG;
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

    /*
     * Final consistency pass for the exact parent/child pair checked by
     * query_operator_model_checker.c.
     */
    igSyncProjectionTypesWithChild(hamming_op);

    INFO_OP_LOG("Rewritten tree for hamming distance", hamming_op);

    if(HAS_STRING_PROP(newProj, IG_PROP_ORIG_ATTR))
	{
		SET_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR,
				copyObject(GET_STRING_PROP(newProj, IG_PROP_ORIG_ATTR)));
	}

    // store the join query
	SET_STRING_PROP(hamming_op, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(newProj, PROP_JOIN_OP_IG)));


    /*
     * Native Hamming already returns the attribute-level DG value as DT_LONG.
     * The old code inserted another materialized projection that only copied
     * hamming_* into value_* and cast the popcount to DT_INT. Downstream
     * stages now consume hamming_* directly.
     */
    return hamming_op;
}

/*
 * Pattern generation returns QueryOperator because the correlation/R^2
 * stage is disabled in the current paper implementation.
 */

static QueryOperator *
rewriteIG_PatternGeneration(ProjectionOperator *priceProj)
{
    ASSERT(OP_LCHILD(priceProj));

    DEBUG_LOG("REWRITE-IG - Pattern Generation");
    DEBUG_LOG("Operator tree \n%s", nodeToString(priceProj));


    /*
     * The CUBE and global totals will share one narrow pattern-input
     * projection.  Build that projection first, then use it as the common
     * child for both consumers.  This keeps the expensive Q_price pipeline
     * single-copy while avoiding materializing its unused ProvW/IG/price_*
     * columns for IGEXPL.
     */
    QueryOperator *totalsInput = NULL;


    List *cleanExprs = NIL;
    List *cleanNames = NIL;

    int cleanPos = 0;

    FOREACH(AttributeDef, a, priceProj->op.schema->attrDefs)
    {
        boolean isProvW =
                isPrefix(a->attrName, "ProvW_")
                || isPrefix(a->attrName, "provw_")
                || isPrefix(a->attrName, "prov_w_");

        boolean isDG =
                isPrefix(a->attrName, "IG_")
                || streq(a->attrName, TOTAL_IG);

        boolean isAttrPrice =
                isPrefix(a->attrName, PRICE_PREFIX);

        boolean isTotalPrice =
                streq(a->attrName, TOTAL_PRICE);


        boolean isPostedPrice = igIsPostedPriceAttr(a->attrName);

//        boolean isLegacyBuyerContext = isPrefix(a->attrName, "a_");

        AttributeReference *ar = createFullAttrReference(a->attrName, 0, cleanPos, 0, a->dataType);

        if(!isDG
                && !isAttrPrice
                && !isTotalPrice
                && !isPostedPrice
                && !isProvW)
        {
            cleanExprs = appendToTailOfList(cleanExprs, ar);

            cleanNames = appendToTailOfList(
                    cleanNames,
                    CONCAT_STRINGS(INDEX, a->attrName));
        }

        else if(isTotalPrice)
        {
            cleanExprs = appendToTailOfList(cleanExprs, ar);
            cleanNames = appendToTailOfList(
                    cleanNames,
                    strdup(a->attrName));
        }


        else if(isPostedPrice)
        {
            cleanExprs = appendToTailOfList(cleanExprs, ar);
            cleanNames = appendToTailOfList(
                    cleanNames,
                    strdup(a->attrName));
        }

        cleanPos++;
    }

    ProjectionOperator *clean = createProjectionOp(cleanExprs, NULL, NIL, cleanNames);

    addChildOperator((QueryOperator *) clean,(QueryOperator *) priceProj);
    switchSubtrees((QueryOperator *) priceProj,(QueryOperator *) clean);

    /*
     * Both GROUP BY CUBE and the denominator aggregation need only the
     * pattern dimensions, posted price, and Total_Price.  Sharing this narrow
     * projection reduces the row width of the materialized common subtree.
     */
    totalsInput = (QueryOperator *) clean;

	List *projNames = NIL;
	List *groupBy = NIL;
	List *aggrs = NIL;


	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
	{
	    /*
	     * Pattern adjusted price:
	     *
	     *      SUM(Total_Price)
	     *
	     * Later normalized into imp.
	     */
	    if(streq(n->attrName, TOTAL_PRICE))
	    {
	        AttributeReference *ar =
	                createFullAttrReference(
	                        n->attrName,
	                        0,
	                        getAttrPos((QueryOperator *) clean, n->attrName),
	                        0,
	                        n->dataType);

	        FunctionCall *sumAdjustedPrice =
	                createFunctionCall(
	                        "SUM",
	                        singleton(ar));

	        sumAdjustedPrice->isAgg = TRUE;

	        aggrs =
	                appendToTailOfList(
	                        aggrs,
	                        sumAdjustedPrice);

	        projNames =
	                appendToTailOfList(
	                        projNames,
	                        strdup(PATTERN_IG));
	    }

	    /*
	     * Pattern posted price:
	     *
	     *      SUM(price) AS p_s
	     */
	    else if(igIsPostedPriceAttr(n->attrName))
	    {
	        AttributeReference *ar =
	                createFullAttrReference(
	                        n->attrName,
	                        0,
	                        getAttrPos((QueryOperator *) clean, n->attrName),
	                        0,
	                        n->dataType);

	        FunctionCall *sumPostedPrice =
	                createFunctionCall(
	                        "SUM",
	                        singleton(ar));

	        sumPostedPrice->isAgg = TRUE;

	        aggrs =
	                appendToTailOfList(
	                        aggrs,
	                        sumPostedPrice);

	        projNames =
	                appendToTailOfList(
	                        projNames,
	                        strdup("p_s"));
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
	    if(streq(n->attrName, PATTERN_IG)
	            || streq(n->attrName, COVERAGE)
	            || streq(n->attrName, "p_s"))
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
		if(streq(n->attrName, PATTERN_IG)
		        || streq(n->attrName, COVERAGE)
		        || streq(n->attrName, "p_s"))
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

//	AttributeReference *cov = getAttrRefByName((QueryOperator *) inform, COVERAGE);
	AttributeReference *inf = getAttrRefByName((QueryOperator *) inform, INFORMATIVENESS);
	AttributeReference *pattIG = getAttrRefByName((QueryOperator *) inform, PATTERN_IG);

//	ADD RULES FOR FILTERING
	/*
	 * Section 5.1, R1:
	 *
	 *      imp > 0
	 *
	 * At this point PATTERN_IG is the unnormalized pattern price:
	 *
	 *      SUM(Total_Price)
	 *
	 * Since every pattern has the same positive normalization
	 * denominator, PATTERN_IG > 0 is equivalent to imp > 0.
	 */
	Node *positiveImpact =
	        (Node *) createOpExpr(
	                OPNAME_GT,
	                LIST_MAKE(
	                    copyObject(pattIG),
	                    igMakeFloatConstInt(0)));

	/*
	 * Section 5.1, R2:
	 *
	 *      info > 0
	 *
	 * At this point informativeness stores the raw number of constants.
	 * This removes the all-placeholder pattern.
	 */
	Node *positiveInfo =
	        (Node *) createOpExpr(
	                OPNAME_GT,
	                LIST_MAKE(
	                    copyObject(inf),
	                    createConstInt(0)));

	Node *finalCond =
	        (Node *) createOpExpr(
	                OPNAME_AND,
	                LIST_MAKE(
	                    positiveImpact,
	                    positiveInfo));

	// this one has removeNoGoodPatt
	SelectionOperator *removeNoGoodPatt = createSelectionOp(finalCond,
			(QueryOperator *) inform, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) inform, (QueryOperator *) removeNoGoodPatt);
	switchSubtrees((QueryOperator *) inform, (QueryOperator *) removeNoGoodPatt);

	INFO_OP_LOG("Remove No Good Patterns: ", removeNoGoodPatt);

	SelectionOperator *topKPattConstPlac = removeNoGoodPatt;

	INFO_OP_LOG("Patterns surviving R1 and R2 filtering: ", topKPattConstPlac);

	/*
	 * Compute the global values required by Definitions 6--8:
	 *
	 *      total_price_all = SUM(Total_Price)
	 *      total_prov_all  = COUNT(*)
	 *
	 * These are computed from Q_price, not from the generated patterns.
	 */

	char *totalPriceAllName = "total_price_all";
	char *totalProvAllName = "total_prov_all";

	List *totalAggrs = NIL;
	List *totalAggrNames = NIL;

	/*
	 * SUM(Total_Price)
	 */
	AttributeReference *allPriceAr =
	        getAttrRefByName(totalsInput, TOTAL_PRICE);

	FunctionCall *sumAllPrice =
	        createFunctionCall("SUM", singleton(allPriceAr));

	sumAllPrice->isAgg = TRUE;

	totalAggrs =
	        appendToTailOfList(totalAggrs, sumAllPrice);

	totalAggrNames =
	        appendToTailOfList(totalAggrNames, totalPriceAllName);

	/*
	 * COUNT(*)
	 */
	FunctionCall *countAllProv =
	        createFunctionCall(
	                "COUNT",
	                singleton(createConstInt(1)));

	countAllProv->isAgg = TRUE;

	totalAggrs =
	        appendToTailOfList(totalAggrs, countAllProv);

	totalAggrNames =
	        appendToTailOfList(totalAggrNames, totalProvAllName);

	AggregationOperator *totalsAggr =
	        createAggregationOp(
	                totalAggrs,
	                NIL,
	                totalsInput,
	                NIL,
	                totalAggrNames);

	addParent(
	        totalsInput,
	        (QueryOperator *) totalsAggr);

	/*
	 * The values are used in floating-point divisions below.
	 */
	FOREACH(AttributeDef, n, totalsAggr->op.schema->attrDefs)
	{
	    n->dataType = DT_FLOAT;
	}

	/*
	 * Attach the global totals to the patterns containing
	 * constants and placeholders.
	 */
	/*
	 * Use the totals aggregation itself.
	 *
	 * The previous copyObject(totalsAggr) cloned totalsAggr together with
	 * its entire Q_price child again.  totalsAggr has only one consumer here,
	 * so copying it is unnecessary and defeats common-subtree reuse.
	 */
	QueryOperator *totalsForConstPlac =
	        (QueryOperator *) totalsAggr;

	List *constPlacInputs =
	        LIST_MAKE(
	                (QueryOperator *) topKPattConstPlac,
	                totalsForConstPlac);

	List *constPlacNames =
	        CONCAT_LISTS(
	                getAttrNames(topKPattConstPlac->op.schema),
	                getAttrNames(totalsForConstPlac->schema));

	QueryOperator *topKPattConstPlacWithTotals =
	        (QueryOperator *) createJoinOp(
	                JOIN_CROSS,
	                NULL,
	                constPlacInputs,
	                NIL,
	                constPlacNames);

	makeAttrNamesUnique(topKPattConstPlacWithTotals);

	addParent(
	        (QueryOperator *) topKPattConstPlac,
	        topKPattConstPlacWithTotals);

	addParent(
	        totalsForConstPlac,
	        topKPattConstPlacWithTotals);

	switchSubtrees(
	        (QueryOperator *) topKPattConstPlac,
	        topKPattConstPlacWithTotals);




    /*
     * First normalize the three ranking metrics in their own projection.
     *
     * Keeping normalization separate from HM is important for two reasons:
     *
     *  1. the generated SQL computes imp/cov/info once instead of repeating
     *     their CASE/division expressions throughout the HM expression; and
     *  2. the parent HM projection can refer to stable child AttributeRefs
     *     whose names and positions match the child AttributeDefs.
     *
     * The raw adjusted pattern price and raw match count are preserved as:
     *
     *      p
     *      match_count
     *
     * The global average adjusted price is also attached once here:
     *
     *      global_avg_p = total_price_all / total_prov_all
     */
    List *metricExprs = NIL;
    List *metricNames = NIL;

    int metricPos = 0;

    AttributeReference *totalPriceAll =
            getAttrRefByName(
                    topKPattConstPlacWithTotals,
                    totalPriceAllName);

    AttributeReference *totalProvAll =
            getAttrRefByName(
                    topKPattConstPlacWithTotals,
                    totalProvAllName);

    ASSERT(totalPriceAll != NULL);
    ASSERT(totalProvAll != NULL);

    FOREACH(AttributeDef, n, topKPattConstPlacWithTotals->schema->attrDefs)
    {
        if(streq(n->attrName, totalPriceAllName)
                || streq(n->attrName, totalProvAllName))
        {
            metricPos++;
            continue;
        }

        AttributeReference *ar =
                createFullAttrReference(
                        n->attrName,
                        0,
                        metricPos,
                        0,
                        n->dataType);

        Node *outExpr = (Node *) ar;
        Node *patternAdjustedPrice = NULL;
        Node *patternMatchCount = NULL;

        if(streq(n->attrName, PATTERN_IG))
        {
            /*
             * Before normalization PATTERN_IG stores:
             *
             *      p = SUM(Total_Price)
             */
            patternAdjustedPrice =
                    (Node *) copyObject(ar);

            /*
             *      imp = p / total_price_all
             */
            outExpr =
                    igSafeDivide(
                            (Node *) ar,
                            (Node *) totalPriceAll);
        }
        else if(streq(n->attrName, COVERAGE))
        {
            /*
             * Before normalization COVERAGE stores COUNT(*).
             */
            patternMatchCount =
                    (Node *) createCastExpr(
                            (Node *) copyObject(ar),
                            DT_INT);

            /*
             *      cov = match_count / total_prov_all
             */
            outExpr =
                    igSafeDivide(
                            (Node *) ar,
                            (Node *) totalProvAll);
        }
        else if(streq(n->attrName, INFORMATIVENESS))
        {
            /*
             *      info = constants / pattern_arity
             */
            outExpr =
                    igSafeDivide(
                            (Node *) ar,
                            igMakeFloatConstInt(num_i));
        }

        metricExprs =
                appendToTailOfList(
                        metricExprs,
                        outExpr);

        metricNames =
                appendToTailOfList(
                        metricNames,
                        strdup(n->attrName));

        if(patternAdjustedPrice != NULL)
        {
            metricExprs =
                    appendToTailOfList(
                            metricExprs,
                            patternAdjustedPrice);

            metricNames =
                    appendToTailOfList(
                            metricNames,
                            strdup("p"));
        }

        if(patternMatchCount != NULL)
        {
            metricExprs =
                    appendToTailOfList(
                            metricExprs,
                            patternMatchCount);

            metricNames =
                    appendToTailOfList(
                            metricNames,
                            strdup(MATCH_COUNT));
        }

        metricPos++;
    }

    Node *globalAvgExpr =
            igSafeDivide(
                    (Node *) copyObject(totalPriceAll),
                    (Node *) copyObject(totalProvAll));

    metricExprs =
            appendToTailOfList(
                    metricExprs,
                    globalAvgExpr);

    metricNames =
            appendToTailOfList(
                    metricNames,
                    strdup(GLOBAL_AVG_PRICE));

    ProjectionOperator *metricNormOp =
            createProjectionOp(
                    metricExprs,
                    topKPattConstPlacWithTotals,
                    NIL,
                    metricNames);

    igSyncProjectionTypesWithChild(metricNormOp);

    addParent(
            topKPattConstPlacWithTotals,
            (QueryOperator *) metricNormOp);

    switchSubtrees(
            topKPattConstPlacWithTotals,
            (QueryOperator *) metricNormOp);

    AttributeDef *metricImpactDef =
            getAttrDefByName(
                    (QueryOperator *) metricNormOp,
                    PATTERN_IG);

    AttributeDef *metricCoverageDef =
            getAttrDefByName(
                    (QueryOperator *) metricNormOp,
                    COVERAGE);

    AttributeDef *metricInfoDef =
            getAttrDefByName(
                    (QueryOperator *) metricNormOp,
                    INFORMATIVENESS);

    AttributeDef *metricPDef =
            getAttrDefByName(
                    (QueryOperator *) metricNormOp,
                    "p");

    AttributeDef *metricCountDef =
            getAttrDefByName(
                    (QueryOperator *) metricNormOp,
                    MATCH_COUNT);

    AttributeDef *metricGlobalAvgDef =
            getAttrDefByName(
                    (QueryOperator *) metricNormOp,
                    GLOBAL_AVG_PRICE);

    ASSERT(metricImpactDef != NULL);
    ASSERT(metricCoverageDef != NULL);
    ASSERT(metricInfoDef != NULL);
    ASSERT(metricPDef != NULL);
    ASSERT(metricCountDef != NULL);
    ASSERT(metricGlobalAvgDef != NULL);

    metricImpactDef->dataType = DT_FLOAT;
    metricCoverageDef->dataType = DT_FLOAT;
    metricInfoDef->dataType = DT_FLOAT;
    metricPDef->dataType = DT_FLOAT;
    metricCountDef->dataType = DT_INT;
    metricGlobalAvgDef->dataType = DT_FLOAT;

    /*
     * Compute HM in a parent projection from the named normalized metrics.
     *
     *                  3 * imp * cov * info
     *      HM = --------------------------------------
     *             imp*cov + imp*info + cov*info
     */
    List *hmExprs = NIL;
    List *hmNames = NIL;
    int hmPos = 0;

    FOREACH(AttributeDef, a, metricNormOp->op.schema->attrDefs)
    {
        hmExprs =
                appendToTailOfList(
                        hmExprs,
                        createFullAttrReference(
                                a->attrName,
                                0,
                                hmPos,
                                0,
                                a->dataType));

        hmNames =
                appendToTailOfList(
                        hmNames,
                        strdup(a->attrName));

        hmPos++;
    }

    AttributeReference *impForScore =
            getAttrRefByName(
                    (QueryOperator *) metricNormOp,
                    PATTERN_IG);

    AttributeReference *covForScore =
            getAttrRefByName(
                    (QueryOperator *) metricNormOp,
                    COVERAGE);

    AttributeReference *infoForScore =
            getAttrRefByName(
                    (QueryOperator *) metricNormOp,
                    INFORMATIVENESS);

    ASSERT(impForScore != NULL);
    ASSERT(covForScore != NULL);
    ASSERT(infoForScore != NULL);

    Node *metricProduct =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(impForScore),
                        copyObject(covForScore),
                        copyObject(infoForScore)));

    Node *hmNumerator =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        igMakeFloatConstInt(3),
                        metricProduct));

    Node *impCov =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(impForScore),
                        copyObject(covForScore)));

    Node *impInfo =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(impForScore),
                        copyObject(infoForScore)));

    Node *covInfo =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(covForScore),
                        copyObject(infoForScore)));

    Node *hmDenominator =
            (Node *) createOpExpr(
                    OPNAME_ADD,
                    LIST_MAKE(
                        impCov,
                        impInfo,
                        covInfo));

    Node *fscoreTopK =
            igSafeDivide(
                    hmNumerator,
                    hmDenominator);

    hmExprs =
            appendToTailOfList(
                    hmExprs,
                    createCastExpr(
                            fscoreTopK,
                            DT_FLOAT));

    hmNames =
            appendToTailOfList(
                    hmNames,
                    strdup(FSCORETOPK));

    ProjectionOperator *fscoreTopKOp =
            createProjectionOp(
                    hmExprs,
                    (QueryOperator *) metricNormOp,
                    NIL,
                    hmNames);

    igSyncProjectionTypesWithChild(fscoreTopKOp);

    AttributeDef *hmDef =
            getAttrDefByName(
                    (QueryOperator *) fscoreTopKOp,
                    FSCORETOPK);

    ASSERT(hmDef != NULL);
    hmDef->dataType = DT_FLOAT;

    addParent(
            (QueryOperator *) metricNormOp,
            (QueryOperator *) fscoreTopKOp);

    switchSubtrees(
            (QueryOperator *) metricNormOp,
            (QueryOperator *) fscoreTopKOp);

    /*
     * Section 5.1, R3: keep only patterns whose average adjusted
     * price is above the global average adjusted price.
     *
     *      price_ratio = imp / cov > 1
     *
     * Since cov > 0 for every generated non-empty CUBE group, this is
     * algebraically equivalent to:
     *
     *      imp > cov
     *
     * Comparing the normalized metrics directly avoids an additional
     * division and any floating-point instability around cov.
     */
    AttributeReference *ratioImpact =
            getAttrRefByName(
                    (QueryOperator *) fscoreTopKOp,
                    PATTERN_IG);

    AttributeReference *ratioCoverage =
            getAttrRefByName(
                    (QueryOperator *) fscoreTopKOp,
                    COVERAGE);

    ASSERT(ratioImpact != NULL);
    ASSERT(ratioCoverage != NULL);

    Node *aboveAveragePrice =
            (Node *) createOpExpr(
                    OPNAME_GT,
                    LIST_MAKE(
                        copyObject(ratioImpact),
                        copyObject(ratioCoverage)));

    SelectionOperator *priceRatioFilter =
            createSelectionOp(
                    aboveAveragePrice,
                    (QueryOperator *) fscoreTopKOp,
                    NIL,
                    getAttrNames(fscoreTopKOp->op.schema));

    addParent(
            (QueryOperator *) fscoreTopKOp,
            (QueryOperator *) priceRatioFilter);

    switchSubtrees(
            (QueryOperator *) fscoreTopKOp,
            (QueryOperator *) priceRatioFilter);

    INFO_OP_LOG(
            "Patterns surviving price_ratio > 1 filtering",
            priceRatioFilter);

	/*
	 * Rank patterns exactly by the paper's score: HM descending.
	 * Pattern attributes are not used as secondary keys.
	 */
	AttributeReference *orderByAr = getAttrRefByName(
	        (QueryOperator *) priceRatioFilter, FSCORETOPK);
	ASSERT(orderByAr != NULL);

	List *orderExprs = singleton(createOrderExpr(
	        (Node *) orderByAr, SORT_DESC, SORT_NULLS_LAST));

	OrderOperator *fscoreTopKOrderBy = createOrderOp(
	        orderExprs, (QueryOperator *) priceRatioFilter, NIL);
	addParent((QueryOperator *) priceRatioFilter,
	        (QueryOperator *) fscoreTopKOrderBy);
	switchSubtrees((QueryOperator *) priceRatioFilter,
	        (QueryOperator *) fscoreTopKOrderBy);

	int k = INT_VALUE((Constant *) topk);
	LimitOperator *fscoreTopKOrderByLimit = createLimitOp(
	        (Node *) createConstInt(k), NULL,
	        (QueryOperator *) fscoreTopKOrderBy, NIL);
	addParent((QueryOperator *) fscoreTopKOrderBy,
	        (QueryOperator *) fscoreTopKOrderByLimit);
	switchSubtrees((QueryOperator *) fscoreTopKOrderBy,
	        (QueryOperator *) fscoreTopKOrderByLimit);

	/* ORDER and LIMIT already preserve the child schema. */
	INFO_OP_LOG("Final top-k explanation patterns Q_pf",
	        fscoreTopKOrderByLimit);
	return (QueryOperator *) fscoreTopKOrderByLimit;
}


/*
 * Return TRUE when a final attribute-level IG column represents an
 * attribute that already belongs to the seller schema.
 *
 * Final IG helper names can escape underscores by doubling them:
 *
 *      arr_delay -> IG_right_arr__delay_integ
 *
 * so compare against both the source spelling and the escaped spelling.
 */
static boolean
igFinalIGMatchesSellerAttr(char *igName, char *sellerAttrName)
{
    if(igName == NULL || sellerAttrName == NULL)
        return FALSE;

    char *suffix = NULL;

    if(isPrefix(igName, "IG_left_"))
        suffix = replaceSubstr(igName, "IG_left_", "");
    else if(isPrefix(igName, "IG_right_"))
        suffix = replaceSubstr(igName, "IG_right_", "");
    else
        return FALSE;

    if(isSuffix(suffix, INTEG_SUFFIX))
        suffix = replaceSubstr(suffix, INTEG_SUFFIX, "");

    char *encodedSellerName = replaceSubstr(sellerAttrName, "_", "__");

    return streq(suffix, sellerAttrName)
            || streq(suffix, encodedSellerName);
}


/*
 * Compute the uniform-pricing denominator from the paper:
 *
 *      | A_new U (Sch(D_s) \ A_new) |
 *      = | A_new U Sch(D_s) |.
 *
 * `attrR` stores the seller-side schema captured at the join rewrite.
 * The seller's posted-price attribute is not purchased data and is
 * therefore excluded.  Internal IG/annotation columns are excluded too.
 *
 * Every final IG_* column represents an A_new attribute.  Seller-side
 * A_new attributes are already counted by Sch(D_s); only A_new attributes
 * that are not physically present in the seller schema add another slot.
 *
 * Running AQI example:
 *      Sch(D_s) data attrs = {year, county, gdays}
 *      extra A_new          = {quality}
 *      scope size           = 4
 *      w_A                  = 1/4
 */
static int
igGetPricingScopeSize(List *igRefs)
{
    int sellerDataAttrCount = 0;
    List *sellerDataAttrNames = NIL;

    FOREACH(AttributeDef, a, attrR)
    {
        if(isPrefix(a->attrName, IG_PREFIX)
                || isSuffix(a->attrName, ANNO_SUFFIX)
                || igIsPostedPriceAttr(a->attrName))
        {
            continue;
        }

        if(searchListString(sellerDataAttrNames, a->attrName) == FALSE)
        {
            sellerDataAttrNames = appendToTailOfList(
                    sellerDataAttrNames,
                    strdup(a->attrName));
            sellerDataAttrCount++;
        }
    }

    int extraANewCount = 0;
    List *extraANewNames = NIL;

    FOREACH(AttributeReference, igAr, igRefs)
    {
        boolean alreadyInSellerSchema = FALSE;

        FOREACH(char, sellerAttrName, sellerDataAttrNames)
        {
            if(igFinalIGMatchesSellerAttr(igAr->name, sellerAttrName))
            {
                alreadyInSellerSchema = TRUE;
                break;
            }
        }

        if(!alreadyInSellerSchema)
        {
            char *scopeName = strdup(igAr->name);

            if(searchListString(extraANewNames, scopeName) == FALSE)
            {
                extraANewNames = appendToTailOfList(
                        extraANewNames,
                        scopeName);
                extraANewCount++;
            }
        }
    }

    DEBUG_LOG(
            "P-XDV pricing scope: %d seller data attrs + %d derived/non-seller A_new attrs = %d",
            sellerDataAttrCount,
            extraANewCount,
            sellerDataAttrCount + extraANewCount);

    return sellerDataAttrCount + extraANewCount;
}


static ProjectionOperator *
rewriteIG_Pricing(ProjectionOperator *cleanProj)
{
    ASSERT(OP_LCHILD(cleanProj));

    DEBUG_LOG("REWRITE-IG - Pricing");
    DEBUG_LOG("Operator tree \n%s", nodeToString(cleanProj));

    List *priceExprs = NIL;
    List *priceNames = NIL;

    /*
     * All attribute-level IG columns that should be priced.
     *
     * This includes both:
     *      IG_left_*
     *      IG_right_*
     *
     * Example:
     *      IG_left_quality_integ
     *      IG_right_gdays_integ
     */
    List *igRefs = NIL;
    List *attrPriceNamesForTotal = NIL;

    int pos = 0;
    boolean hasPostedPriceColumn = FALSE;
    /*
     * Keep clean output columns and collect IG columns.
     */
    FOREACH(AttributeDef, a, cleanProj->op.schema->attrDefs)
    {
    	if(igIsPostedPriceAttr(a->attrName))
    	{
    	    hasPostedPriceColumn = TRUE;
    	}
        AttributeReference *ar = createFullAttrReference(
                a->attrName,
                0,
                pos,
                0,
                a->dataType);

        /*
         * Collect all final IG columns for pricing.
         * Do not collect Total_IG here because it is not prefix IG_.
         */
        if(isPrefix(a->attrName, "IG_"))
        {
            AttributeReference *igAr = createFullAttrReference(
                    a->attrName,
                    0,
                    pos,
                    0,
                    a->dataType);

            igRefs = appendToTailOfList(igRefs, igAr);
        }

        /*
         * Keep clean display columns.
         * This removes internal helper columns but keeps:
         *      IG_*
         *      Total_IG
         *      normal output attrs
         *      provenance attrs
         */
        if(!igIsConvertedOutputAttr(a->attrName))
        {
            priceExprs = appendToTailOfList(priceExprs, ar);
            priceNames = appendToTailOfList(priceNames, a->attrName);
        }

        pos++;
    }

    /*
     * Posted seller price pi.
     * Uses price/base_price/posted_price/ps/p_s/b_price if present;
     * otherwise falls back to DEFAULT_TUPLE_PRICE.
     */
    Node *postedPrice = igGetPostedPriceExpr(cleanProj);
    /*
     * Make the posted tuple price visible in Q_price.
     *
     * When the input already contains a posted-price column,
     * that column has already been preserved above.
     *
     * Otherwise expose the fallback price as:
     *
     *      p_s
     */
    if(!hasPostedPriceColumn)
    {
        priceExprs =
                appendToTailOfList(
                        priceExprs,
                        copyObject(postedPrice));

        priceNames =
                appendToTailOfList(
                        priceNames,
                        strdup("p_s"));
    }

    /*
     * Uniform attribute weight from the paper.
     *
     * The default weight is
     *
     *      w_A = 1 / | A_new U (Sch(D_s) \ A_new) |
     *          = 1 / | A_new U Sch(D_s) |.
     *
     * The posted-price attribute itself is metadata, not part of the
     * purchased data tuple, so it is excluded from Sch(D_s) here.
     * A derived priced attribute (for example, AQI quality) is added
     * to the scope when it is not already present in the seller schema.
     *
     * With lambda = 0.5, the base-price term becomes
     *
     *      (1-lambda) * w_A * p_s
     *      = p_s / (2 * pricingScopeSize).
     */
    int pricingScopeSize = igGetPricingScopeSize(igRefs);

    if(igRefs != NIL && LIST_LENGTH(igRefs) > 0)
    {
        ASSERT(pricingScopeSize > 0);
        DEBUG_LOG(
                "P-XDV pricing: uniform weight w_A = 1/%d = %f",
                pricingScopeSize,
                1.0 / (double) pricingScopeSize);
    }

    /*
     * If there are no IG columns, still add Total_Price = 0.
     */
    if(igRefs == NIL || LIST_LENGTH(igRefs) == 0)
    {
        priceExprs = appendToTailOfList(priceExprs, igMakeFloatConstInt(0));
        priceNames = appendToTailOfList(priceNames, strdup(TOTAL_PRICE));
    }
    else
    {
        /*
         * Denominator:
         *      DG(pt)
         *
         * This is the sum of all attribute-level IG/DG columns.
         * Example:
         *      IG_left_quality_integ + IG_right_gdays_integ
         */
        Node *priceTotalIG = igMakeSumOrSingle(copyObject(igRefs));

        /*
         * For each IG column, create the corresponding price column.
         *
         * The paper's default parameters are:
         *
         *      lambda = 0.5
         *      w_A = 1 / pricingScopeSize
         *
         * Therefore:
         *
         *      price(A)
         *        = pi / (2 * pricingScopeSize)
         *          + pi * IG(A) / (2 * TotalIG)
         *
         * If IG(A) = 0, then price(A) = 0.
         */
        FOREACH(AttributeReference, igAr, igRefs)
        {
            Node *igVal = (Node *) copyObject(igAr);

            Node *igGtZero = (Node *) createOpExpr(
                    OPNAME_GT,
                    LIST_MAKE(copyObject(igVal), createConstInt(0)));

            Node *totalGtZero = (Node *) createOpExpr(
                    OPNAME_GT,
                    LIST_MAKE(copyObject(priceTotalIG), createConstInt(0)));

            Node *cond = (Node *) createOpExpr(
                    OPNAME_AND,
                    LIST_MAKE(igGtZero, totalGtZero));

            /*
             * leftPart = (1-lambda) * w_A * pi
             *          = pi / (2 * pricingScopeSize)
             * for lambda = 0.5 and uniform w_A.
             */
            Node *leftPart = (Node *) createOpExpr(
                    OPNAME_DIV,
                    LIST_MAKE(
                        createCastExpr(copyObject(postedPrice), DT_FLOAT),
                        igMakeFloatConstInt(2 * pricingScopeSize)));

            /*
             * rightPart = pi * IG(A) / (2 * TotalIG)
             */
            Node *numerator = (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        createCastExpr(copyObject(postedPrice), DT_FLOAT),
                        createCastExpr(copyObject(igVal), DT_FLOAT)));

            Node *denominator = (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        igMakeFloatConstInt(2),
                        createCastExpr(copyObject(priceTotalIG), DT_FLOAT)));

            Node *rightPart = (Node *) createOpExpr(
                    OPNAME_DIV,
                    LIST_MAKE(numerator, denominator));

            Node *priceRaw = (Node *) createOpExpr(
                    OPNAME_ADD,
                    LIST_MAKE(leftPart, rightPart));

            CaseWhen *cw = createCaseWhen(cond, priceRaw);

            CaseExpr *priceCase = createCaseExpr(
                    NULL,
                    singleton(cw),
                    igMakeFloatConstInt(0));

            priceExprs = appendToTailOfList(priceExprs, priceCase);

            /*
             * Column name:
             *
             *      IG_left_quality_integ  -> price_left_quality
             *      IG_right_gdays_integ   -> price_right_gdays
             */
            char *suffix = replaceSubstr(igAr->name, "IG_", "");
            suffix = replaceSubstr(suffix, INTEG_SUFFIX, "");

            char *priceName = CONCAT_STRINGS(PRICE_PREFIX, suffix);

            priceNames = appendToTailOfList(priceNames, priceName);

            attrPriceNamesForTotal = appendToTailOfList(
                    attrPriceNamesForTotal,
                    strdup(priceName));
        }

        /*
         * Attribute-level price expressions are computed once in the lower
         * pricing projection. Total_Price is added in a thin parent
         * projection by summing the named price_* columns.
         */
    }

    ProjectionOperator *priceProj = NULL;
    ProjectionOperator *attrPriceProj = NULL;

    if(igRefs == NIL || LIST_LENGTH(igRefs) == 0)
    {
        /* No priced attributes: Total_Price = 0 is already present. */
        priceProj = createProjectionOp(priceExprs, NULL, NIL, priceNames);

        addChildOperator((QueryOperator *) priceProj, (QueryOperator *) cleanProj);
        switchSubtrees((QueryOperator *) cleanProj, (QueryOperator *) priceProj);

        igSyncProjectionRefsWithChild(priceProj);
    }
    else
    {
        /*
         * Layer 1: compute price_A columns exactly once.
         */
        attrPriceProj = createProjectionOp(priceExprs, NULL, NIL, priceNames);

        FOREACH(AttributeDef, n, attrPriceProj->op.schema->attrDefs)
        {
            if(isPrefix(n->attrName, PRICE_PREFIX))
                n->dataType = DT_FLOAT;
        }

        addChildOperator((QueryOperator *) attrPriceProj, (QueryOperator *) cleanProj);
        switchSubtrees((QueryOperator *) cleanProj, (QueryOperator *) attrPriceProj);

        igSyncProjectionRefsWithChild(attrPriceProj);

        /*
         * Layer 2: pass through Layer-1 columns at identical positions and
         * append Total_Price = sum(price_*).
         */
        List *totalExprs = NIL;
        List *totalNames = NIL;
        List *attrPriceRefsForTotal = NIL;
        int totalPos = 0;

        FOREACH(AttributeDef, a, attrPriceProj->op.schema->attrDefs)
        {
            AttributeReference *ar = createFullAttrReference(
                    a->attrName, 0, totalPos, 0, a->dataType);

            totalExprs = appendToTailOfList(totalExprs, ar);
            totalNames = appendToTailOfList(
                    totalNames, strdup(a->attrName));

            if(searchListString(attrPriceNamesForTotal, a->attrName))
            {
                attrPriceRefsForTotal = appendToTailOfList(
                        attrPriceRefsForTotal, copyObject(ar));
            }

            totalPos++;
        }

        ASSERT(attrPriceRefsForTotal != NIL);

        totalExprs = appendToTailOfList(
                totalExprs,
                igMakeSumOrSingle(attrPriceRefsForTotal));
        totalNames = appendToTailOfList(
                totalNames,
                strdup(TOTAL_PRICE));

        priceProj = createProjectionOp(
                totalExprs, NULL, NIL, totalNames);

        addChildOperator(
                (QueryOperator *) priceProj,
                (QueryOperator *) attrPriceProj);
        switchSubtrees(
                (QueryOperator *) attrPriceProj,
                (QueryOperator *) priceProj);

        igSyncProjectionRefsWithChild(priceProj);
    }

    /*
     * Make price columns FLOAT.
     */
    FOREACH(AttributeDef, n, priceProj->op.schema->attrDefs)
    {
        if(isPrefix(n->attrName, PRICE_PREFIX)
                || streq(n->attrName, TOTAL_PRICE))
        {
            n->dataType = DT_FLOAT;
        }
    }

    /*
     * Final display order to match Figure 1:
     *
     *      1. Q output
     *      2. buyer table provenance: a_*
     *      3. seller table provenance: b_*
     *      4. value provenance: ProvW_*
     *      5. DG columns: IG_* and Total_IG
     *      6. price columns: ps / price_* / Total_Price
     */
    List *qExprs = NIL;
    List *qDefs = NIL;

    List *aProvExprs = NIL;
    List *aProvDefs = NIL;

    List *bProvExprs = NIL;
    List *bProvDefs = NIL;

    List *provWExprs = NIL;
    List *provWDefs = NIL;

    List *dgExprs = NIL;
    List *dgDefs = NIL;

    List *totalDGExprs = NIL;
    List *totalDGDefs = NIL;

    List *postedPriceExprs = NIL;
    List *postedPriceDefs = NIL;

    List *attrPriceExprs = NIL;
    List *attrPriceDefs = NIL;

    List *totalPriceExprs = NIL;
    List *totalPriceDefs = NIL;

    int reorderPos = 0;

    FOREACH(AttributeDef, a, priceProj->op.schema->attrDefs)
    {
        Node *expr = (Node *) getNthOfListP(priceProj->projExprs, reorderPos);

        if(isPrefix(a->attrName, "a_"))
        {
            aProvExprs = appendToTailOfList(aProvExprs, expr);
            aProvDefs = appendToTailOfList(aProvDefs, a);
        }

        else if(isPrefix(a->attrName, "b_"))
        {
            bProvExprs = appendToTailOfList(bProvExprs, expr);
            bProvDefs = appendToTailOfList(bProvDefs, a);
        }
        else if(isPrefix(a->attrName, "ProvW_")
                || isPrefix(a->attrName, "provw_")
                || isPrefix(a->attrName, "prov_w_"))
        {
            provWExprs = appendToTailOfList(provWExprs, expr);
            provWDefs = appendToTailOfList(provWDefs, a);
        }
        else if(isPrefix(a->attrName, "IG_"))
        {
            dgExprs = appendToTailOfList(dgExprs, expr);
            dgDefs = appendToTailOfList(dgDefs, a);
        }
        else if(streq(a->attrName, TOTAL_IG))
        {
            totalDGExprs = appendToTailOfList(totalDGExprs, expr);
            totalDGDefs = appendToTailOfList(totalDGDefs, a);
        }
        else if(streq(a->attrName, "price")
                || streq(a->attrName, "base_price")
                || streq(a->attrName, "posted_price")
                || streq(a->attrName, "ps")
                || streq(a->attrName, "p_s")
                || streq(a->attrName, "b_price"))
        {
            postedPriceExprs = appendToTailOfList(postedPriceExprs, expr);
            postedPriceDefs = appendToTailOfList(postedPriceDefs, a);
        }
        else if(isPrefix(a->attrName, PRICE_PREFIX))
        {
            attrPriceExprs = appendToTailOfList(attrPriceExprs, expr);
            attrPriceDefs = appendToTailOfList(attrPriceDefs, a);
        }
        else if(streq(a->attrName, TOTAL_PRICE))
        {
            totalPriceExprs = appendToTailOfList(totalPriceExprs, expr);
            totalPriceDefs = appendToTailOfList(totalPriceDefs, a);
        }
        else
        {
            /*
             * Normal query output attributes.
             *
             * Example:
             *      year, county, quality
             */
            qExprs = appendToTailOfList(qExprs, expr);
            qDefs = appendToTailOfList(qDefs, a);
        }

        reorderPos++;
    }

    List *allDGExprs = CONCAT_LISTS(dgExprs, totalDGExprs);
    List *allDGDefs = CONCAT_LISTS(dgDefs, totalDGDefs);

    List *allPriceExprs = CONCAT_LISTS(postedPriceExprs,
            CONCAT_LISTS(attrPriceExprs, totalPriceExprs));

    List *allPriceDefs = CONCAT_LISTS(postedPriceDefs,
            CONCAT_LISTS(attrPriceDefs, totalPriceDefs));

    priceProj->projExprs =
            CONCAT_LISTS(qExprs,
            CONCAT_LISTS(aProvExprs,
            CONCAT_LISTS(bProvExprs,
            CONCAT_LISTS(provWExprs,
            CONCAT_LISTS(allDGExprs, allPriceExprs)))));

    priceProj->op.schema->attrDefs =
            CONCAT_LISTS(qDefs,
            CONCAT_LISTS(aProvDefs,
            CONCAT_LISTS(bProvDefs,
            CONCAT_LISTS(provWDefs,
            CONCAT_LISTS(allDGDefs, allPriceDefs)))));

    /*
     * The output-order rewrite above does not change child positions, but
     * normalize references once more before returning the projection.
     */
    igSyncProjectionRefsWithChild(priceProj);

    return priceProj;
}


/*
 * Final presentation-only rounding for IG output.
 *
 * Keep all internal DG and pricing computations at full precision.  This
 * projection is added only after Q_price has been fully computed and only for
 * the user-facing IG result.  Thus rounding cannot change Total_Price,
 * explanation ranking, impact, coverage, HM, or any later computation.
 *
 * Round only P-XDV monetary outputs:
 *      posted price (p_s / price / ...)
 *      price_*
 *      Total_Price
 *
 * Normal query attributes and provenance values are preserved exactly, even
 * if their source data type is floating point.
 */
static ProjectionOperator *
rewriteIG_RoundFinalNumericOutput(ProjectionOperator *priceProj)
{
    ASSERT(priceProj != NULL);

    List *exprs = NIL;
    List *names = NIL;
    int pos = 0;

    FOREACH(AttributeDef, a, priceProj->op.schema->attrDefs)
    {
        AttributeReference *ar =
                createFullAttrReference(
                        a->attrName,
                        0,
                        pos,
                        0,
                        a->dataType);

        boolean roundTo2 =
                igIsPostedPriceAttr(a->attrName)
                || isPrefix(a->attrName, PRICE_PREFIX)
                || streq(a->attrName, TOTAL_PRICE);

        if(roundTo2)
            exprs = appendToTailOfList(exprs, igRound2((Node *) ar));
        else
            exprs = appendToTailOfList(exprs, ar);

        names = appendToTailOfList(names, strdup(a->attrName));
        pos++;
    }

    ProjectionOperator *rounded =
            createProjectionOp(
                    exprs,
                    (QueryOperator *) priceProj,
                    NIL,
                    names);

    addParent(
            (QueryOperator *) priceProj,
            (QueryOperator *) rounded);

    switchSubtrees(
            (QueryOperator *) priceProj,
            (QueryOperator *) rounded);

    /*
     * igRound2 returns FLOAT expressions.  Keep schema typing explicit for
     * every rounded monetary output.
     */
    FOREACH(AttributeDef, a, rounded->op.schema->attrDefs)
    {
        if(igIsPostedPriceAttr(a->attrName)
                || isPrefix(a->attrName, PRICE_PREFIX)
                || streq(a->attrName, TOTAL_PRICE))
        {
            a->dataType = DT_FLOAT;
        }
    }

    return rounded;
}

static boolean
igIsConvertedOutputAttr(char *attrName)
{
    /*
     * Keep all final IG columns and Total_IG in the output.
     * This includes names such as:
     *
     *      IG_right_gdays_integ
     *      IG_left_quality_integ
     *      Total_IG
     *
     * Even though some IG columns contain "_integ", they are final
     * output DG/IG columns, not temporary helper columns.
     */
    if(isPrefix(attrName, "IG_") || streq(attrName, "Total_IG"))
        return FALSE;

    /*
     * Remove internal converted/helper columns.
     */
    return isPrefix(attrName, "ig_conv_left_")
        || isPrefix(attrName, "ig_conv_right_")
        || isPrefix(attrName, HAMMING_PREFIX)
        || isSubstr(attrName, INTEG_SUFFIX);
}

static boolean
igIsPostedPriceAttr(char *attrName)
{
    if(attrName == NULL)
        return FALSE;

    return streq(attrName, "price")
        || streq(attrName, "base_price")
        || streq(attrName, "posted_price")
        || streq(attrName, "ps")
        || streq(attrName, "p_s")
        || streq(attrName, "b_price");
}

// function to round float to 2 decimal places
static Node *
igRound2(Node *expr)
{
    Node *scaled =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        createCastExpr(copyObject(expr), DT_FLOAT),
                        igMakeFloatConstInt(100)));

    FunctionCall *rounded =
            createFunctionCall(
                    "ROUND",
                    singleton(scaled));

    Node *res =
            (Node *) createOpExpr(
                    OPNAME_DIV,
                    LIST_MAKE(
                        rounded,
                        igMakeFloatConstInt(100)));

    return (Node *) createCastExpr(res, DT_FLOAT);
}

static Node *
igMakeFloatConstInt(int v)
{
    return (Node *) createCastExpr((Node *) createConstInt(v), DT_FLOAT);
}


static Node *
igMakeSumOrSingle(List *exprs)
{
    if(exprs == NIL || LIST_LENGTH(exprs) == 0)
        return igMakeFloatConstInt(0);

    if(LIST_LENGTH(exprs) == 1)
        return (Node *) copyObject(getHeadOfListP(exprs));

    return (Node *) createOpExpr(OPNAME_ADD, exprs);
}

// get the price attribute
static Node *
igGetPostedPriceExpr(ProjectionOperator *cleanProj)
{
    int pos = 0;

    FOREACH(AttributeDef, a, cleanProj->op.schema->attrDefs)
    {
        if(igIsPostedPriceAttr(a->attrName))
        {
            /*
             * shared.price is an integer, but that is fine.
             * The pricing expressions cast it to float later.
             */
            return (Node *) createFullAttrReference(
                    a->attrName,
                    0,
                    pos,
                    0,
                    a->dataType);
        }

        pos++;
    }

    /*
     * Fallback only. If shared.price exists and the rewrite is correct,
     * we should not get here.
     */
    WARN_LOG("No posted-price column found in Q_price input. "
             "Using DEFAULT_TUPLE_PRICE = %d",
             DEFAULT_TUPLE_PRICE);

    return (Node *) createConstInt(DEFAULT_TUPLE_PRICE);
}

/*
 * Returns an attribute only when the original SELECT item directly
 * projects that attribute.
 *
 */

static AttributeReference *
igGetDirectProjectedAttr(Node *expr)
{
    if(isA(expr, AttributeReference))
        return (AttributeReference *) expr;

    return NULL;
}


/*
 * Locate the actual ig_conv_left_* / ig_conv_right_* attribute that
 * corresponds to a source attribute.  Do not synthesize this name from
 * the source identifier: generated helper names escape underscores, e.g.
 *
 *      delay_status -> ig_conv_left_delay__status
 *
 * The join model may also make a duplicate right-side attribute unique by
 * appending a trailing "1" (delay_status1).  We first try the exact name;
 * only if that fails do we try the same name with that uniqueness suffix
 * removed.
 */
static AttributeReference *
igFindConvertedAttr(
        QueryOperator *op,
        char *baseName,
        boolean rightSide)
{
    if(op == NULL || baseName == NULL)
        return NULL;

    char *prefix = rightSide
            ? "ig_conv_right_"
            : "ig_conv_left_";

    char *baseExact = strdup(baseName);
    char *baseWithoutJoinSuffix = NULL;

    int baseLen = strlen(baseName);
    if(baseLen > 1 && baseName[baseLen - 1] == '1')
    {
        baseWithoutJoinSuffix = strdup(baseName);
        baseWithoutJoinSuffix[baseLen - 1] = '\0';
    }

    int pos = 0;
    FOREACH(AttributeDef, a, op->schema->attrDefs)
    {
        if(isPrefix(a->attrName, prefix)
                && !isSuffix(a->attrName, INTEG_SUFFIX))
        {
            char *suffix = replaceSubstr(a->attrName, prefix, "");
            char *encodedExact = replaceSubstr(baseExact, "_", "__");

            boolean matches =
                    streq(suffix, baseExact)
                    || streq(suffix, encodedExact);

            if(!matches && baseWithoutJoinSuffix != NULL)
            {
                char *encodedNoSuffix =
                        replaceSubstr(baseWithoutJoinSuffix, "_", "__");

                matches =
                        streq(suffix, baseWithoutJoinSuffix)
                        || streq(suffix, encodedNoSuffix);
            }

            if(matches)
            {
                return createFullAttrReference(
                        a->attrName,
                        0,
                        pos,
                        0,
                        a->dataType);
            }
        }

        pos++;
    }

    return NULL;
}


static AttributeReference *
igGetAttrRefAny(QueryOperator *op, char *name1, char *name2)
{
    if(name1 != NULL && getAttrPos(op, name1) >= 0)
        return getAttrRefByName(op, name1);

    if(name2 != NULL && getAttrPos(op, name2) >= 0)
        return getAttrRefByName(op, name2);

    return NULL;
}


static Node *
igConcatText(List *parts)
{
    if(parts == NIL || LIST_LENGTH(parts) == 0)
        return (Node *) createConstString("");

    /*
     * concatExprList creates the SQL concatenation expression.
     * The explicit cast ensures that schema inference sees a string.
     */
    return (Node *) createCastExpr(
            concatExprList(
                    (List *) copyObject(parts)),
            DT_STRING);
}


static Node *
igText(Node *expr)
{
    return (Node *) createCastExpr(
            copyObject(expr),
            DT_STRING);
}


/*
 * Safe floating-point division:
 *
 *      denominator > 0
 *          ? numerator / denominator
 *          : 0
 */
static Node *
igSafeDivide(Node *numerator, Node *denominator)
{
    Node *positiveDenominator =
            (Node *) createOpExpr(
                    OPNAME_GT,
                    LIST_MAKE(
                        copyObject(denominator),
                        igMakeFloatConstInt(0)));

    Node *division =
            (Node *) createOpExpr(
                    OPNAME_DIV,
                    LIST_MAKE(
                        createCastExpr(
                                copyObject(numerator),
                                DT_FLOAT),
                        createCastExpr(
                                copyObject(denominator),
                                DT_FLOAT)));

    return (Node *) createCaseExpr(
            NULL,
            singleton(
                createCaseWhen(
                        positiveDenominator,
                        division)),
            igMakeFloatConstInt(0));
}


/*
 * A NULL CUBE dimension represents "*".
 *
 * Generate the supplied sentence only when the dimension is a constant.
 */
static Node *
igWhenPresent(AttributeReference *ar, Node *text)
{
    Node *present =
            (Node *) createOpExpr(
                    OPNAME_NOT,
                    singleton(
                        createIsNullExpr(
                                (Node *) copyObject(ar))));

    return (Node *) createCaseExpr(
            NULL,
            singleton(
                createCaseWhen(
                        present,
                        text)),
            (Node *) createConstString(""));
}


/*
 * Compare an integrated output value with its owner-side value.
 *
 * Examples:
 *
 *      quality = unhealthy
 *      a_quality = normal
 *
 * becomes:
 *
 *      The integrated output quality changed from the owner's
 *      value normal to unhealthy.
 *
 * The statement is generated only when both values are constants
 * in the current pattern. If either value is "*", nothing is claimed.
 */
static Node *
igOwnerChangeText(
        AttributeReference *integrated,
        AttributeReference *owner,
        char *attrName)
{
    Node *integratedPresent =
            (Node *) createOpExpr(
                    OPNAME_NOT,
                    singleton(
                        createIsNullExpr(
                                (Node *) copyObject(integrated))));

    Node *ownerPresent =
            (Node *) createOpExpr(
                    OPNAME_NOT,
                    singleton(
                        createIsNullExpr(
                                (Node *) copyObject(owner))));

    Node *bothPresent =
            (Node *) createOpExpr(
                    OPNAME_AND,
                    LIST_MAKE(
                        integratedPresent,
                        ownerPresent));

    /*
     * Compare text representations so that the same code works for
     * strings, integers, and other visible attribute types.
     */
    Node *equalValues =
            (Node *) createOpExpr(
                    OPNAME_EQ,
                    LIST_MAKE(
                        igText(
                                (Node *) integrated),
                        igText(
                                (Node *) owner)));

    Node *differentValues =
            (Node *) createOpExpr(
                    OPNAME_NOT,
                    singleton(
                        copyObject(equalValues)));

    Node *changedCondition =
            (Node *) createOpExpr(
                    OPNAME_AND,
                    LIST_MAKE(
                        copyObject(bothPresent),
                        differentValues));

    Node *sameCondition =
            (Node *) createOpExpr(
                    OPNAME_AND,
                    LIST_MAKE(
                        bothPresent,
                        equalValues));

    Node *changedText =
            igConcatText(
                    LIST_MAKE(
                        createConstString(
                                "The integrated output "),
                        createConstString(
                                attrName),
                        createConstString(
                                " changed from the owners value "),
                        igText(
                                (Node *) owner),
                        createConstString(
                                " to "),
                        igText(
                                (Node *) integrated),
                        createConstString(
                                ". ")));

    Node *sameText =
            igConcatText(
                    LIST_MAKE(
                        createConstString(
                                "The integrated output "),
                        createConstString(
                                attrName),
                        createConstString(
                                " remained "),
                        igText(
                                (Node *) integrated),
                        createConstString(
                                ". ")));

    return (Node *) createCaseExpr(
            NULL,
            LIST_MAKE(
                createCaseWhen(
                        changedCondition,
                        changedText),
                createCaseWhen(
                        sameCondition,
                        sameText)),
            (Node *) createConstString(""));
}


/*
 * Add source-aware numerical and textual explanations to Q_pf.
 *
 * Final output:
 *
 *      dimensions,
 *      p_s,
 *      p,
 *      imp,
 *      cov,
 *      info,
 *      hm,
 *      match_count,
 *      avg_p,
 *      global_avg_p,
 *      price_ratio,
 *      relative_pct,
 *      discount_pct,
 *      explanation
 */
static QueryOperator *
rewriteIG_PatternExplanations(QueryOperator *patterns)
{
    ASSERT(patterns != NULL);

    AttributeReference *p =
            igGetAttrRefAny(
                    patterns,
                    "p",
                    NULL);

    AttributeReference *postedPrice =
            igGetAttrRefAny(
                    patterns,
                    "p_s",
                    NULL);

    AttributeReference *impact =
            igGetAttrRefAny(
                    patterns,
                    PATTERN_IG,
                    "pattern_ig");

    AttributeReference *coverage =
            igGetAttrRefAny(
                    patterns,
                    COVERAGE,
                    "cov");

    AttributeReference *informativeness =
            igGetAttrRefAny(
                    patterns,
                    INFORMATIVENESS,
                    "info");

    AttributeReference *hm =
            igGetAttrRefAny(
                    patterns,
                    FSCORETOPK,
                    "fscoretopk");

    AttributeReference *matchCount =
            igGetAttrRefAny(
                    patterns,
                    MATCH_COUNT,
                    NULL);

    AttributeReference *globalAvgBase =
            igGetAttrRefAny(
                    patterns,
                    GLOBAL_AVG_PRICE,
                    NULL);

    ASSERT(p != NULL);
    ASSERT(postedPrice != NULL);
    ASSERT(impact != NULL);
    ASSERT(coverage != NULL);
    ASSERT(informativeness != NULL);
    ASSERT(hm != NULL);
    ASSERT(matchCount != NULL);
    ASSERT(globalAvgBase != NULL);

    /*
     * Collect the actual pattern dimensions.
     *
     * Pattern generation places the CUBE dimensions first:
     *
     *      i_year
     *      i_county
     *      i_quality
     *      ...
     *
     * followed by the pattern metrics.
     *
     * Do not scan the entire schema later and assume that every
     * i_* attribute anywhere in the schema is a pattern dimension.
     */
    List *patternDimensionNames = NIL;
    boolean collectingPatternDimensions = TRUE;

    FOREACH(AttributeDef, a, patterns->schema->attrDefs)
    {
        if(collectingPatternDimensions
                && isPrefix(a->attrName, INDEX))
        {
            patternDimensionNames =
                    appendToTailOfList(
                            patternDimensionNames,
                            strdup(a->attrName));

            DEBUG_LOG(
                    "P-XDV actual pattern dimension: %s",
                    a->attrName);
        }
        else if(patternDimensionNames != NIL)
        {
            /*
             * Once the first non-dimension column is reached,
             * the pattern-dimension section is finished.
             */
            collectingPatternDimensions = FALSE;
        }
    }

    /*
     * Compute interpretation metrics once in an intermediate projection.
     *
     * Previously avg_p, price_ratio, global_avg_p, relative_pct, and
     * discount_pct were expanded repeatedly in both the user-facing output
     * columns and the explanation text.  That made the generated SQL large
     * and repeated the same CASE/division expressions many times.
     *
     * global_avg_p was already computed once during pattern normalization
     * from:
     *
     *      total_price_all / total_prov_all
     *
     * and is simply carried through here.
     */
    Node *avgPriceExpr =
            igSafeDivide(
                    (Node *) copyObject(p),
                    (Node *) copyObject(matchCount));

    Node *priceRatioExpr =
            igSafeDivide(
                    (Node *) copyObject(impact),
                    (Node *) copyObject(coverage));

    Node *relativePctExpr =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        createOpExpr(
                                OPNAME_MINUS,
                                LIST_MAKE(
                                    copyObject(priceRatioExpr),
                                    igMakeFloatConstInt(1))),
                        igMakeFloatConstInt(100)));

    Node *discountNumerator =
            (Node *) createOpExpr(
                    OPNAME_MINUS,
                    LIST_MAKE(
                        copyObject(postedPrice),
                        copyObject(p)));

    Node *discountPctExpr =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        igSafeDivide(
                                discountNumerator,
                                (Node *) copyObject(postedPrice)),
                        igMakeFloatConstInt(100)));

    List *interpretExprs = NIL;
    List *interpretNames = NIL;
    int interpretPos = 0;

    FOREACH(AttributeDef, a, patterns->schema->attrDefs)
    {
        interpretExprs =
                appendToTailOfList(
                        interpretExprs,
                        createFullAttrReference(
                                a->attrName,
                                0,
                                interpretPos,
                                0,
                                a->dataType));

        interpretNames =
                appendToTailOfList(
                        interpretNames,
                        strdup(a->attrName));

        interpretPos++;
    }

    interpretExprs =
            appendToTailOfList(
                    interpretExprs,
                    avgPriceExpr);

    interpretNames =
            appendToTailOfList(
                    interpretNames,
                    strdup(AVG_PRICE));

    interpretExprs =
            appendToTailOfList(
                    interpretExprs,
                    priceRatioExpr);

    interpretNames =
            appendToTailOfList(
                    interpretNames,
                    strdup(PRICE_RATIO));

    interpretExprs =
            appendToTailOfList(
                    interpretExprs,
                    relativePctExpr);

    interpretNames =
            appendToTailOfList(
                    interpretNames,
                    strdup(RELATIVE_PCT));

    interpretExprs =
            appendToTailOfList(
                    interpretExprs,
                    discountPctExpr);

    interpretNames =
            appendToTailOfList(
                    interpretNames,
                    strdup(DISCOUNT_PCT));

    ProjectionOperator *interpretMetrics =
            createProjectionOp(
                    interpretExprs,
                    patterns,
                    NIL,
                    interpretNames);

    igSyncProjectionTypesWithChild(interpretMetrics);

    AttributeDef *avgPriceDef =
            getAttrDefByName(
                    (QueryOperator *) interpretMetrics,
                    AVG_PRICE);

    AttributeDef *priceRatioDef =
            getAttrDefByName(
                    (QueryOperator *) interpretMetrics,
                    PRICE_RATIO);

    AttributeDef *relativePctDef =
            getAttrDefByName(
                    (QueryOperator *) interpretMetrics,
                    RELATIVE_PCT);

    AttributeDef *discountPctDef =
            getAttrDefByName(
                    (QueryOperator *) interpretMetrics,
                    DISCOUNT_PCT);

    ASSERT(avgPriceDef != NULL);
    ASSERT(priceRatioDef != NULL);
    ASSERT(relativePctDef != NULL);
    ASSERT(discountPctDef != NULL);

    avgPriceDef->dataType = DT_FLOAT;
    priceRatioDef->dataType = DT_FLOAT;
    relativePctDef->dataType = DT_FLOAT;
    discountPctDef->dataType = DT_FLOAT;

    addParent(
            patterns,
            (QueryOperator *) interpretMetrics);

    switchSubtrees(
            patterns,
            (QueryOperator *) interpretMetrics);

    /*
     * The active explanation input is now the metric projection.  Rebind all
     * AttributeReferences against this child so GProM's name/position/type
     * invariants remain exact.
     */
    patterns = (QueryOperator *) interpretMetrics;

    p =
            igGetAttrRefAny(
                    patterns,
                    "p",
                    NULL);

    postedPrice =
            igGetAttrRefAny(
                    patterns,
                    "p_s",
                    NULL);

    impact =
            igGetAttrRefAny(
                    patterns,
                    PATTERN_IG,
                    "pattern_ig");

    coverage =
            igGetAttrRefAny(
                    patterns,
                    COVERAGE,
                    "cov");

    informativeness =
            igGetAttrRefAny(
                    patterns,
                    INFORMATIVENESS,
                    "info");

    hm =
            igGetAttrRefAny(
                    patterns,
                    FSCORETOPK,
                    "fscoretopk");

    matchCount =
            igGetAttrRefAny(
                    patterns,
                    MATCH_COUNT,
                    NULL);

    AttributeReference *avgPrice =
            igGetAttrRefAny(
                    patterns,
                    AVG_PRICE,
                    NULL);

    AttributeReference *globalAvgPrice =
            igGetAttrRefAny(
                    patterns,
                    GLOBAL_AVG_PRICE,
                    NULL);

    AttributeReference *priceRatio =
            igGetAttrRefAny(
                    patterns,
                    PRICE_RATIO,
                    NULL);

    AttributeReference *relativePct =
            igGetAttrRefAny(
                    patterns,
                    RELATIVE_PCT,
                    NULL);

    AttributeReference *discountPct =
            igGetAttrRefAny(
                    patterns,
                    DISCOUNT_PCT,
                    NULL);

    ASSERT(p != NULL);
    ASSERT(postedPrice != NULL);
    ASSERT(impact != NULL);
    ASSERT(coverage != NULL);
    ASSERT(informativeness != NULL);
    ASSERT(hm != NULL);
    ASSERT(matchCount != NULL);
    ASSERT(avgPrice != NULL);
    ASSERT(globalAvgPrice != NULL);
    ASSERT(priceRatio != NULL);
    ASSERT(relativePct != NULL);
    ASSERT(discountPct != NULL);

    /*
     * Build source-aware descriptions of each pattern constant.
     *
     *      a_*       -> owner value
     *      b_*       -> sharer value
     *      join attr -> matched owner and sharer value
     *      otherwise -> integrated output value
     */
    List *contextParts = NIL;

    FOREACH(char, dimensionName, patternDimensionNames)
    {
        AttributeReference *dimension =
                getAttrRefByName(
                        patterns,
                        dimensionName);

        char *baseName =
                replaceSubstr(
                        dimensionName,
                        INDEX,
                        "");

        Node *sentence = NULL;

        /*
         * Owner-side pattern dimension.
         *
         * Example:
         *
         *      i_a_quality
         */
        if(isPrefix(baseName, "a_"))
        {
            char *ownerAttr =
                    replaceSubstr(
                            baseName,
                            "a_",
                            "");

            sentence =
                    igConcatText(
                            LIST_MAKE(
                                createConstString(
                                        "The owners "),
                                createConstString(
                                        ownerAttr),
                                createConstString(
                                        " value is "),
                                igText(
                                        (Node *) dimension),
                                createConstString(
                                        ". ")));
        }

        /*
         * Sharer-side pattern dimension.
         *
         * Example:
         *
         *      i_b_gdays
         */
        else if(isPrefix(baseName, "b_"))
        {
            char *sharerAttr =
                    replaceSubstr(
                            baseName,
                            "b_",
                            "");

            sentence =
                    igConcatText(
                            LIST_MAKE(
                                createConstString(
                                        "The sharers "),
                                createConstString(
                                        sharerAttr),
                                createConstString(
                                        " value is "),
                                igText(
                                        (Node *) dimension),
                                createConstString(
                                        ". ")));
        }

        /*
         * Common join attribute.
         *
         * Examples:
         *
         *      year
         *      county
         */
        else if(searchListString(
                        igJoinAttrNames,
                        baseName))
        {
            sentence =
                    igConcatText(
                            LIST_MAKE(
                                createConstString(
                                        "The join attribute "),
                                createConstString(
                                        baseName),
                                createConstString(
                                        " is "),
                                igText(
                                        (Node *) dimension),
                                createConstString(
                                        ". ")));
        }

        /*
         * Remaining unprefixed pattern dimensions are integrated
         * query-output values.
         */
        else
        {
            sentence =
                    igConcatText(
                            LIST_MAKE(
                                createConstString(
                                        "The integrated output "),
                                createConstString(
                                        baseName),
                                createConstString(
                                        " is "),
                                igText(
                                        (Node *) dimension),
                                createConstString(
                                        ". ")));
        }

        /*
         * Only include the sentence when the pattern has a constant
         * instead of "*".
         */
        contextParts =
                appendToTailOfList(
                        contextParts,
                        igWhenPresent(
                                dimension,
                                sentence));
    }


    FOREACH(char, dimensionName, patternDimensionNames)
    {
        char *baseName =
                replaceSubstr(
                        dimensionName,
                        INDEX,
                        "");
        /*
         * Start only from an integrated dimension.
         */
        if(isPrefix(baseName, "a_")
                || isPrefix(baseName, "b_"))
        {
            continue;
        }

        char *ownerPatternName =
                CONCAT_STRINGS(
                        INDEX,
                        "a_");

        ownerPatternName =
                CONCAT_STRINGS(
                        ownerPatternName,
                        baseName);

        if(getAttrPos(
                patterns,
                ownerPatternName) >= 0)
        {
        	AttributeReference *integrated =
        	        getAttrRefByName(
        	                patterns,
        	                dimensionName);

            AttributeReference *owner =
                    getAttrRefByName(
                            patterns,
                            ownerPatternName);

            contextParts =
                    appendToTailOfList(
                            contextParts,
                            igOwnerChangeText(
                                    integrated,
                                    owner,
                                    baseName));
        }
    }

    /*
     * Singular/plural tuple wording.
     */
    Node *oneMatch =
            (Node *) createOpExpr(
                    OPNAME_EQ,
                    LIST_MAKE(
                        copyObject(matchCount),
                        createConstInt(1)));

    Node *tupleWord =
            (Node *) createCaseExpr(
                    NULL,
                    singleton(
                        createCaseWhen(
                            oneMatch,
                            (Node *) createConstString(
                                    " tuple"))),
                    (Node *) createConstString(
                            " tuples"));

    /*
     * Produce:
     *
     *      25% above
     *      equal to
     *      8.33% below
     */
    Node *roundedRelative =
            igRound2(
                    copyObject(relativePct));

    Node *aboveAverage =
            (Node *) createOpExpr(
                    OPNAME_GT,
                    LIST_MAKE(
                        copyObject(roundedRelative),
                        igMakeFloatConstInt(0)));

    Node *belowAverage =
            (Node *) createOpExpr(
                    OPNAME_LT,
                    LIST_MAKE(
                        copyObject(roundedRelative),
                        igMakeFloatConstInt(0)));

    Node *belowMagnitude =
            (Node *) createOpExpr(
                    OPNAME_MINUS,
                    LIST_MAKE(
                        igMakeFloatConstInt(0),
                        copyObject(relativePct)));

    Node *aboveText =
            igConcatText(
                    LIST_MAKE(
                        igText(
                            igRound2(
                                    copyObject(relativePct))),
                        createConstString(
                                "% above")));

    Node *belowText =
            igConcatText(
                    LIST_MAKE(
                        igText(
                            igRound2(
                                    belowMagnitude)),
                        createConstString(
                                "% below")));

    Node *relativeText =
            (Node *) createCaseExpr(
                    NULL,
                    LIST_MAKE(
                        createCaseWhen(
                                aboveAverage,
                                aboveText),
                        createCaseWhen(
                                belowAverage,
                                belowText)),
                    (Node *) createConstString(
                            "equal to"));

    /*
     * Convert normalized metrics to percentages for the text.
     */
    Node *coveragePct =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(coverage),
                        igMakeFloatConstInt(100)));

    Node *impactPct =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(impact),
                        igMakeFloatConstInt(100)));

    Node *infoPct =
            (Node *) createOpExpr(
                    OPNAME_MULT,
                    LIST_MAKE(
                        copyObject(informativeness),
                        igMakeFloatConstInt(100)));

    /*
     * Build the complete textual explanation.
     */
    List *explanationParts = NIL;

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            "This pattern matches "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                            (Node *) matchCount));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    tupleWord);

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            ". "));

    /*
     * Append all source-aware pattern descriptions.
     */
    FOREACH(Node, contextPart, contextParts)
    {
        explanationParts =
                appendToTailOfList(
                        explanationParts,
                        contextPart);
    }

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            "It covers "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                coveragePct)));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            "% of the query result and accounts for "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                impactPct)));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            "% of total adjusted payment. "
                            "Its average adjusted price is "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                copyObject(avgPrice))));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            ", which is "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    relativeText);

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            " the global average of "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                copyObject(globalAvgPrice))));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            ". The combined posted price is "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                (Node *) postedPrice)));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            " and the adjusted price is "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                (Node *) p)));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            ", giving a "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                copyObject(discountPct))));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            "% discount. "
                            "The pattern informativeness is "));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    igText(
                        igRound2(
                                infoPct)));

    explanationParts =
            appendToTailOfList(
                    explanationParts,
                    createConstString(
                            "%."));

    Node *explanationText =
            igConcatText(
                    explanationParts);

    /*
     * Build the final user-facing output.
     *
     * Do not create another cleanup projection after this operator.
     */
    List *outExprs = NIL;
    List *outNames = NIL;

    /*
     * Pattern dimensions first.
     *
     * Reuse the exact dimension list collected above.  This makes the
     * user-facing projection independent of internal metric columns and
     * prevents fields such as the internal `informativeness` attribute
     * from leaking into the final output next to the renamed `info`.
     */
    FOREACH(char, dimensionName, patternDimensionNames)
    {
        int dimensionPos = getAttrPos(patterns, dimensionName);
        AttributeDef *dimensionDef =
                getAttrDefByName(patterns, dimensionName);

        ASSERT(dimensionPos >= 0);
        ASSERT(dimensionDef != NULL);

        outExprs =
                appendToTailOfList(
                        outExprs,
                        createFullAttrReference(
                                dimensionName,
                                0,
                                dimensionPos,
                                0,
                                dimensionDef->dataType));

        outNames =
                appendToTailOfList(
                        outNames,
                        replaceSubstr(
                                dimensionName,
                                INDEX,
                                ""));
    }

    /*
     * Posted and adjusted prices.
     */
    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            (Node *) postedPrice));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup("p_s"));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            (Node *) p));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup("p"));

    /*
     * Main pattern metrics.
     *
     * Explicitly rename:
     *
     *      pattern_IG      -> imp
     *      coverage        -> cov
     *      informativeness -> info
     *      fscoreTopK      -> hm
     */
    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            (Node *) impact));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup("imp"));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            (Node *) coverage));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup("cov"));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            (Node *) informativeness));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup("info"));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            (Node *) hm));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup("hm"));

    /*
     * Additional interpretation metrics.
     */
    outExprs =
            appendToTailOfList(
                    outExprs,
                    copyObject(matchCount));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(MATCH_COUNT));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            copyObject(avgPrice)));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(AVG_PRICE));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            copyObject(globalAvgPrice)));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(GLOBAL_AVG_PRICE));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            copyObject(priceRatio)));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(PRICE_RATIO));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            copyObject(relativePct)));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(RELATIVE_PCT));

    outExprs =
            appendToTailOfList(
                    outExprs,
                    igRound2(
                            copyObject(discountPct)));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(DISCOUNT_PCT));

    /*
     * Text output.
     *
     * The additional cast prevents the columns from disappearing
     * because of uncertain expression type inference.
     */
    outExprs =
            appendToTailOfList(
                    outExprs,
                    createCastExpr(
                            copyObject(explanationText),
                            DT_STRING));

    outNames =
            appendToTailOfList(
                    outNames,
                    strdup(EXPLANATION_TEXT));

    ProjectionOperator *result =
            createProjectionOp(
                    outExprs,
                    patterns,
                    NIL,
                    outNames);

    addParent(
            patterns,
            (QueryOperator *) result);

    /*
     * Important:
     *
     * The old code created the projection but did not replace the active
     * pattern branch. Without this call, generated text may not reach
     * the final SQL query.
     */
    switchSubtrees(
            patterns,
            (QueryOperator *) result);

    /*
     * Explicit output schema types.
     */
    getAttrDefByName(
            (QueryOperator *) result,
            "p_s")->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            "p")->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            "imp")->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            "cov")->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            "info")->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            "hm")->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            MATCH_COUNT)->dataType = DT_INT;

    getAttrDefByName(
            (QueryOperator *) result,
            AVG_PRICE)->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            GLOBAL_AVG_PRICE)->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            PRICE_RATIO)->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            RELATIVE_PCT)->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            DISCOUNT_PCT)->dataType = DT_FLOAT;

    getAttrDefByName(
            (QueryOperator *) result,
            EXPLANATION_TEXT)->dataType = DT_STRING;

    INFO_OP_LOG(
            "Final source-aware pattern explanations",
            result);

    return (QueryOperator *) result;
}


/*
 * Recursively refresh every AttributeReference inside an expression against
 * the current child schema. getAttrReferences() walks the full expression
 * tree, so nested CASE/AND/OR/IS NULL/functions/arithmetic are handled
 * without a fixed nesting depth.
 */
static void
igRefreshExprRefsAgainstChild(Node *expr, QueryOperator *child)
{
    if(expr == NULL || child == NULL)
        return;

    List *refs = getAttrReferences(expr);

    FOREACH(AttributeReference, ar, refs)
    {
        int attrPos = getAttrPos(child, ar->name);

        if(attrPos >= 0)
        {
            AttributeDef *childDef = getAttrDefByPos(child, attrPos);
            ar->attrPosition = attrPos;

            if(childDef != NULL)
                ar->attrType = childDef->dataType;
        }
    }
}


/*
 * Resolve JOIN condition references from the source side and local position,
 * not by bare column name.  This matters when both inputs have names such as
 * flight_id, year, or month.
 *
 * GProM can still print its early duplicate-name warning before P-XDV runs;
 * this helper prevents duplicate names from becoming ambiguous inside P-XDV.
 */
static void
igNormalizeJoinCondRefsBySide(
        JoinOperator *op,
        QueryOperator *lChild,
        QueryOperator *rChild)
{
    if(op == NULL || op->cond == NULL || lChild == NULL || rChild == NULL)
        return;

    List *refs = getAttrReferences(op->cond);

    FOREACH(AttributeReference, ar, refs)
    {
        QueryOperator *source = NULL;

        if(ar->fromClauseItem == 0)
            source = lChild;
        else if(ar->fromClauseItem == 1)
            source = rChild;

        if(source == NULL)
            continue;

        int localPos = ar->attrPosition;

        if(localPos < 0
                || localPos >= LIST_LENGTH(source->schema->attrDefs))
            continue;

        AttributeDef *sourceDef = getAttrDefByPos(source, localPos);

        if(sourceDef != NULL)
        {
            ar->name = strdup(sourceDef->attrName);
            ar->attrType = sourceDef->dataType;
        }
    }
}


static QueryOperator *
rewriteIG_Projection (ProjectionOperator *op)
{
    ASSERT(OP_LCHILD(op));
    DEBUG_LOG("REWRITE-IG - Integration");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    // store original attributes in the input query
	List *origAttrs = copyObject(op->projExprs);

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

    List *directBuyerAttrs = NIL;
    int leftLen = LIST_LENGTH(attrL);

    FOREACH(Node, expr, origAttrs)
    {
        AttributeReference *ar = igGetDirectProjectedAttr(expr);

        if(ar != NULL
                && ar->attrPosition >= 0
                && ar->attrPosition < leftLen
                && searchListString(directBuyerAttrs, ar->name) == FALSE)
        {
            directBuyerAttrs = appendToTailOfList(
                    directBuyerAttrs,
                    strdup(ar->name));
        }
    }


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

            /*
             * Keep the actual join-attribute names for source-aware
             * explanation text.  Do this from the parsed join predicates
             * instead of hard-coding year/county or any dataset-specific
             * attribute names.
             */
            char *joinName = strdup(ar->name);

            if(isSuffix(joinName, "1"))
                joinName = replaceSubstr(joinName, "1", "");

            if(searchListString(igJoinAttrNames, joinName) == FALSE)
                igJoinAttrNames = appendToTailOfList(
                        igJoinAttrNames,
                        joinName);
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

    // add IG attributes and refresh CASE references recursively
	FOREACH(Node, n, op->projExprs)
	{
		if(isA(n, CaseExpr))
		{
            /*
             * One recursive walk refreshes references in every WHEN, THEN,
             * ELSE, nested CASE, AND/OR, IS NULL, function, and arithmetic
             * expression contained in this CASE.
             */
            igRefreshExprRefsAgainstChild(n, child);
			newProjExpr = appendToTailOfList(newProjExpr, n);
		}
		else
		{
			AttributeReference *a = (AttributeReference *) n;
			AttributeReference *ar = createFullAttrReference(
                    a->name,
                    0,
                    getAttrPos((QueryOperator *) child, a->name),
                    0,
                    a->attrType);

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


	FOREACH(AttributeDef, la, attrL)
	{
	    if(isPrefix(la->attrName, IG_PREFIX)
	            || isSuffix(la->attrName, ANNO_SUFFIX)
	            || igIsPostedPriceAttr(la->attrName))
	    {
	        continue;
	    }

	    /*
	     * The original query already directly displays this buyer value.
	     */
	    if(searchListString(directBuyerAttrs, la->attrName))
	        continue;

	    char *outputName = CONCAT_STRINGS("a_", la->attrName);

	    /*
	     * Defensive duplicate check.
	     */
	    if(searchListString(newAttrNames, outputName))
	        continue;

	    int lpos = getAttrPos((QueryOperator *) child, la->attrName);

	    if(lpos >= 0)
	    {
	        AttributeReference *lar = createFullAttrReference(
	                la->attrName,
	                0,
	                lpos,
	                0,
	                la->dataType);

	        newProjExprWithCaseWhen = appendToTailOfList(
	                newProjExprWithCaseWhen,
	                lar);

	        newAttrNames = appendToTailOfList(
	                newAttrNames,
	                outputName);
	    }
	}


	/*
	 * Seller-side tuple provenance (Prov_h): b_*
	 *
	 * Definition 1 in the paper keeps a seller attribute A only when
	 * it is query-relevant and does not already exist in the buyer
	 * schema:
	 *
	 *      A in Q intersect Sch(D_s)  and  A notin Sch(D_r)
	 *
	 * The existing right-side converted IG column is our signal that
	 * the seller attribute was captured as query-relevant.  However,
	 * the existence of ig_conv_right_* alone is NOT sufficient: the
	 * conversion code can also create right-side helper columns for
	 * attributes with the same name in both inputs.  Such a helper
	 * must not become seller Prov_h.
	 *
	 * Example:
	 *      buyer:  quality
	 *      seller: quality
	 *
	 * Even if ig_conv_right_quality exists internally, b_quality must
	 * not be materialized because quality already belongs to Sch(D_r).
	 * For the AQI query, b_gdays is retained because gdays is used by
	 * Q and does not exist in the buyer schema.
	 *
	 * This rule is schema/query driven; no AQI attribute name is
	 * hard-coded, so a different query may produce a different set of
	 * b_* provenance attributes.
	 */
	FOREACH(AttributeDef, ra, attrR)
	{
	    boolean existsInBuyer =
	            MAP_HAS_STRING_KEY(attrLNames, ra->attrName);

	    char *rightIGPrefix = CONCAT_STRINGS(IG_PREFIX, "conv_");
	    rightIGPrefix = CONCAT_STRINGS(rightIGPrefix, IG_RIGHT);

	    char *rightIGName = CONCAT_STRINGS(rightIGPrefix, ra->attrName);

	    /*
	     * A seller attribute is query-relevant when the rewrite captured
	     * it for conversion/DG (projection, CASE, selection, etc.) or
	     * when it occurs in the join predicate itself.  The latter keeps
	     * the implementation aligned with Definition 1 for joins whose
	     * seller-side key has a different name and therefore does not
	     * occur in the buyer schema.
	     */
	    boolean isQueryRelevant =
	            getAttrPos((QueryOperator *) child, rightIGName) >= 0
	            || searchListString(joinAttrs, ra->attrName);

		if(!isPrefix(ra->attrName, IG_PREFIX)
		        && !isSuffix(ra->attrName, ANNO_SUFFIX)
		        && !igIsPostedPriceAttr(ra->attrName)
		        && !existsInBuyer
		        && isQueryRelevant)
	    {
	            int rpos = getAttrPos((QueryOperator *) child, ra->attrName);
	            char *refName = ra->attrName;

	            /*
	             * Fallback for attributes made unique by the join.
	             * For valid seller-only Prov_h attributes this should
	             * rarely be needed, but keeping it preserves the
	             * existing rewrite behavior.
	             */
	            if(rpos < 0)
	            {
	                refName = CONCAT_STRINGS(ra->attrName, "1");
	                rpos = getAttrPos((QueryOperator *) child, refName);
	            }

	        if(rpos >= 0)
	        {
	            AttributeReference *rar = createFullAttrReference(
	                    refName,
	                    0,
	                    rpos,
	                    0,
	                    ra->dataType);

	            newProjExprWithCaseWhen = appendToTailOfList(
	                    newProjExprWithCaseWhen,
	                    rar);

	            newAttrNames = appendToTailOfList(
	                    newAttrNames,
	                    CONCAT_STRINGS("b_", ra->attrName));
	        }
	    }
	}


    boolean hasPostedPriceInProj =
            searchListString(newAttrNames, "price")
            || searchListString(newAttrNames, "base_price")
            || searchListString(newAttrNames, "posted_price")
            || searchListString(newAttrNames, "ps")
            || searchListString(newAttrNames, "p_s")
            || searchListString(newAttrNames, "b_price");

    if(!hasPostedPriceInProj)
    {
        FOREACH(AttributeDef, ra, attrR)
        {
            if(igIsPostedPriceAttr(ra->attrName))
            {
                char *refName = ra->attrName;
                int rpos = getAttrPos((QueryOperator *) child, refName);

                /*
                 * If the join made right-side duplicate names unique,
                 * the seller column may appear as price1.
                 */
                if(rpos < 0)
                {
                    refName = CONCAT_STRINGS(ra->attrName, "1");
                    rpos = getAttrPos((QueryOperator *) child, refName);
                }

                if(rpos >= 0)
                {
                    AttributeReference *priceAr =
                            createFullAttrReference(
                                    refName,
                                    0,
                                    rpos,
                                    0,
                                    ra->dataType);

                    newProjExprWithCaseWhen =
                            appendToTailOfList(
                                    newProjExprWithCaseWhen,
                                    priceAr);

                    /*
                     * Expose seller posted price under a stable internal name.
                     * rewriteIG_Pricing() and pattern generation already
                     * recognize p_s as a posted-price column.
                     */
                    newAttrNames =
                            appendToTailOfList(
                                    newAttrNames,
                                    strdup("p_s"));

                    DEBUG_LOG(
                            "P-XDV: carrying seller posted price <%s> as p_s",
                            refName);

                    break;
                }
            }
        }
    }

	/*
	 * 3. Value provenance display: ProvW_*
	 *
	 * For every left-side converted IG column, display the original
	 * buyer-side value that the integrated output is compared against.
	 *
	 * Running example:
	 *      ig_conv_left_quality -> ProvW_quality
	 */
	List *provWBaseNames = NIL;

	FOREACH(AttributeDef, ca, child->schema->attrDefs)
	{
	    char *leftIGPrefix = CONCAT_STRINGS(IG_PREFIX, "conv_");
	    leftIGPrefix = CONCAT_STRINGS(leftIGPrefix, IG_LEFT);

	    if(ca->dataType == DT_LONG && isPrefix(ca->attrName, leftIGPrefix))
	    {
	        char *baseName = replaceSubstr(ca->attrName, leftIGPrefix, "");

	        if(searchListString(provWBaseNames, baseName) == FALSE)
	        {
	            int basePos = getAttrPos((QueryOperator *) child, baseName);

	            if(basePos >= 0)
	            {
	                AttributeDef *baseDef = getAttrDefByName((QueryOperator *) child, baseName);

	                AttributeReference *provWAr = createFullAttrReference(
	                        baseName,
	                        0,
	                        basePos,
	                        0,
	                        baseDef->dataType);

	                newProjExprWithCaseWhen = appendToTailOfList(
	                        newProjExprWithCaseWhen,
	                        provWAr);

	                newAttrNames = appendToTailOfList(
	                        newAttrNames,
	                        CONCAT_STRINGS("ProvW_", baseName));

	                provWBaseNames = appendToTailOfList(provWBaseNames, baseName);
	            }
	        }
	    }
	}


    FOREACH(AttributeDef, a, child->schema->attrDefs)
    {
    	/* Only converted IG helpers belong in igAttrs; ordinary BIGINT
    	 * columns such as flight_id must not be treated as provenance values. */
    	if(isPrefix(a->attrName, IG_PREFIX))
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
    			adlIg->dataType = DT_LONG;

    			AttributeDef *adrIg = (AttributeDef *) copyObject(MAP_GET_STRING(attrRNames, a->attrName));
    			adrIg->attrName = igNameR;
    			adrIg->dataType = DT_LONG;

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

    // adding IG attributes after integration
    //
    // IMPORTANT: use the converted attributes that actually exist in the
    // rewritten child.  Do not reconstruct helper names from tblNameL/R.
    // Identifiers containing underscores are escaped in generated helper
    // names (e.g., delay_status -> delay__status), which caused CASE arms
    // to remain ordinary INT values while another arm was converted to BIT.
    FOREACH(Node, n, op->projExprs)
    {
        if(!isA(n, CaseExpr))
        {
            AttributeReference *ar = (AttributeReference *) n;
            int sourcePos = getAttrPos((QueryOperator *) child, ar->name);
            boolean rightSide = sourcePos >= leftLen;

            AttributeReference *igExpr =
                    igFindConvertedAttr(
                            (QueryOperator *) child,
                            ar->name,
                            rightSide);

            if(igExpr != NULL)
            {
                addIgExprs = appendToTailOfList(
                        addIgExprs,
                        (Node *) copyObject(igExpr));

                addIgAttrs = appendToTailOfList(
                        addIgAttrs,
                        CONCAT_STRINGS(igExpr->name, INTEG_SUFFIX));
            }
        }
        else
        {
            CaseExpr *ce = copyObject((CaseExpr *) n);

            /*
             * Prefer a buyer-side converted result as the comparison
             * baseline for a derived value.  This implements the Prov_w
             * interpretation used by P-XDV: compare the integrated value
             * with the buyer's corresponding original value when one exists.
             * If no buyer-side result exists, fall back to a seller-side
             * converted result (which can then be compared with zero).
             */
            AttributeReference *leftBaseline = NULL;
            AttributeReference *anyBaseline = NULL;

            FOREACH(CaseWhen, cw, ce->whenClauses)
            {
                if(isA(cw->then, AttributeReference))
                {
                    AttributeReference *thenAr =
                            (AttributeReference *) cw->then;

                    int sourcePos =
                            getAttrPos((QueryOperator *) child, thenAr->name);

                    boolean rightSide = sourcePos >= leftLen;

                    AttributeReference *converted =
                            igFindConvertedAttr(
                                    (QueryOperator *) child,
                                    thenAr->name,
                                    rightSide);

                    if(converted != NULL)
                    {
                        cw->then = (Node *) copyObject(converted);

                        if(anyBaseline == NULL)
                            anyBaseline =
                                    (AttributeReference *) copyObject(converted);

                        if(!rightSide && leftBaseline == NULL)
                            leftBaseline =
                                    (AttributeReference *) copyObject(converted);
                    }
                }
                else if(isA(cw->then, Constant))
                {
                    /*
                     * Numeric CASE constants participate in the binary DG
                     * representation.  Casting here keeps all CASE result
                     * branches type-compatible in PostgreSQL.
                     */
                    Constant *c = (Constant *) cw->then;
                    if(c->constType == DT_INT
                            || c->constType == DT_LONG
                            || c->constType == DT_FLOAT)
                    {
                        cw->then =
                                (Node *) createCastExpr(
                                        copyObject(cw->then),
                                        DT_LONG);
                    }
                }
            }

            if(isA(ce->elseRes, AttributeReference))
            {
                AttributeReference *elseAr =
                        (AttributeReference *) ce->elseRes;

                int sourcePos =
                        getAttrPos((QueryOperator *) child, elseAr->name);

                boolean rightSide = sourcePos >= leftLen;

                AttributeReference *converted =
                        igFindConvertedAttr(
                                (QueryOperator *) child,
                                elseAr->name,
                                rightSide);

                if(converted != NULL)
                {
                    ce->elseRes = (Node *) copyObject(converted);

                    if(anyBaseline == NULL)
                        anyBaseline =
                                (AttributeReference *) copyObject(converted);

                    if(!rightSide && leftBaseline == NULL)
                        leftBaseline =
                                (AttributeReference *) copyObject(converted);
                }
            }
            else if(isA(ce->elseRes, Constant))
            {
                Constant *c = (Constant *) ce->elseRes;
                if(c->constType == DT_INT
                        || c->constType == DT_LONG
                        || c->constType == DT_FLOAT)
                {
                    ce->elseRes =
                            (Node *) createCastExpr(
                                    copyObject(ce->elseRes),
                                    DT_LONG);
                }
            }

            AttributeReference *baseline =
                    leftBaseline != NULL
                    ? leftBaseline
                    : anyBaseline;

            if(baseline != NULL)
            {
                addIgExprs = appendToTailOfList(addIgExprs, ce);
                addIgAttrs = appendToTailOfList(
                        addIgAttrs,
                        CONCAT_STRINGS(baseline->name, INTEG_SUFFIX));
            }
            else
            {
                WARN_LOG(
                        "P-XDV: no converted CASE result attribute found; "
                        "skipping integrated DG helper for this CASE expression");
            }
        }
    }

    /*
     * BUG FIX:
     *
     * Add integrated DG columns for right-side/seller-only attributes
     * that were captured because they occur in CASE WHEN conditions,
     * but are not themselves projected by the input query.
     *
     * Example:
     *      CASE WHEN (... b.gdays <= 70) THEN ...
     *
     * TableAccess already created:
     *      ig_conv_right_gdays
     *
     * But the old code never created:
     *      ig_conv_right_gdays_integ
     *
     * Without the _integ column, rewriteIG_HammingFunctions() never
     * computes:
     *      hamming_right_gdays_integ
     *      value_right_gdays_integ
     *      IG_right_gdays_integ
     */
    char *rightConvPrefix = CONCAT_STRINGS(IG_PREFIX, "conv_");
    rightConvPrefix = CONCAT_STRINGS(rightConvPrefix, IG_RIGHT);

    char *leftConvPrefix = CONCAT_STRINGS(IG_PREFIX, "conv_");
    leftConvPrefix = CONCAT_STRINGS(leftConvPrefix, IG_LEFT);

    FOREACH(AttributeDef, a, child->schema->attrDefs)
    {
        if(a->dataType == DT_LONG && isPrefix(a->attrName, rightConvPrefix))
        {
            /*
             * Example:
             *      rightAttrName = ig_conv_right_gdays
             *      leftAttrName  = ig_conv_left_gdays
             *
             * If the left version does not exist, this is seller-only data.
             * It should be compared with 0 according to DG case (3).
             */
            char *rightAttrName = a->attrName;
            char *leftAttrName = replaceSubstr(
                    rightAttrName,
                    rightConvPrefix,
                    leftConvPrefix);
            char *rightIntegName = CONCAT_STRINGS(rightAttrName, INTEG_SUFFIX);
            char *baseAttrName = replaceSubstr(
                    rightAttrName,
                    rightConvPrefix,
                    "");

            /*
             * Case (3) of DG is for seller-only query-relevant attributes.
             * Absence of an ig_conv_left_* helper is NOT enough to conclude
             * that an attribute is seller-only.  For example, s.maqi may occur
             * only in a CASE condition while maqi also exists in the buyer
             * schema; the buyer-side maqi then may have no conversion helper.
             *
             * Use the actual buyer schema (attrLNames) to decide seller-only
             * status.  This prevents a same-named seller predicate attribute
             * from incorrectly becoming a separate DG dimension compared with 0.
             */
            boolean existsInBuyerSchema =
                    MAP_HAS_STRING_KEY(attrLNames, baseAttrName);

            if(!existsInBuyerSchema
                    && !MAP_HAS_STRING_KEY(igAttrs, leftAttrName)
                    && searchListString(addIgAttrs, rightIntegName) == FALSE)
            {
                AttributeReference *rightAr = createFullAttrReference(
                        rightAttrName,
                        0,
                        getAttrPos((QueryOperator *) child, rightAttrName),
                        0,
                        a->dataType);

                /*
                 * For seller-only attributes:
                 *
                 *      ig_conv_right_gdays_integ = ig_conv_right_gdays
                 *
                 * Hamming will then compare it against 0.
                 */
                addIgExprs = appendToTailOfList(addIgExprs, rightAr);
                addIgAttrs = appendToTailOfList(addIgAttrs, rightIntegName);
            }
        }
    }

    List *allExprs = CONCAT_LISTS(newProjExprWithCaseWhen,addIgExprs);
    List *allAttrs = CONCAT_LISTS(newAttrNames,addIgAttrs);

	ProjectionOperator *newProj1 = createProjectionOp(allExprs, NULL, NIL, allAttrs);
    addChildOperator((QueryOperator *) newProj1, (QueryOperator *) child);
    switchSubtrees((QueryOperator *) op, (QueryOperator *) newProj1);

    // All IG conversion columns use signed 64-bit integer encoding.
    FOREACH(AttributeDef, ad, newProj1->op.schema->attrDefs)
    {
    	if(isPrefix(ad->attrName,IG_PREFIX))
    		ad->dataType = DT_LONG;
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

    /*
     * Synchronize both nested AttributeReference types and output AttributeDefs
     * after the expression rewrite.  This prevents stale DT_BIT10 metadata
     * from surviving inside CASE/CAST expressions.
     */
    igSyncProjectionTypesWithChild(newProj1);

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

        SET_STRING_PROP(newProj1, IG_PROP_ORIG_ATTR, origAttrs);

    // store the join query
	SET_STRING_PROP(newProj1, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(op, PROP_JOIN_OP_IG)));


    INFO_OP_LOG("Rewritten Operator tree for all IG attributes", newProj1);

//  Add native attribute-level Hamming/DG columns.
	ProjectionOperator *hamming_op = rewriteIG_HammingFunctions(newProj1);

	/*
	 * Give attribute-level DG columns their final IG_* names and compute
	 * Total_IG. This replaces the old hamming_* -> value_* compatibility
	 * projection and the subsequent value_* -> IG_* rename projection.
	 */
	ProjectionOperator *sumrows = rewriteIG_SumExprs(hamming_op);

	SET_STRING_PROP(sumrows, IG_INPUT_DEFS_PROP,
	        copyObject(op->op.schema->attrDefs));

	ProjectionOperator *priceProj = rewriteIG_Pricing(sumrows);

	if(explFlag == FALSE)
	{
	    /*
	     * Round only the final user-facing monetary columns.
	     * Internal pricing above remains full precision.
	     */
	    ProjectionOperator *roundedPriceOutput =
	            rewriteIG_RoundFinalNumericOutput(priceProj);

	    INFO_OP_LOG(
	            "Rewritten Operator tree with prices rounded to 2 decimals",
	            (QueryOperator *) roundedPriceOutput);

	    return (QueryOperator *) roundedPriceOutput;
	}
	else
	{
	    /*
	     * Generate top-k explanation patterns.
	     */
	    QueryOperator *patterns =
	            rewriteIG_PatternGeneration(
	                    priceProj);

	    INFO_OP_LOG(
	            "Rewritten Operator tree for patterns",
	            patterns);

	    /*
	     * Add final metrics and natural-language explanation.
	     */
	    QueryOperator *result =
	            rewriteIG_PatternExplanations(
	                    patterns);

	    INFO_OP_LOG(
	            "Final P-XDV pattern output with explanations",
	            result);

	    return result;
	}
}

static QueryOperator *
rewriteIG_Join (JoinOperator *op)
{
    DEBUG_LOG("REWRITE-IG - Join");

    QueryOperator *lChild = OP_LCHILD(op);
    QueryOperator *rChild = OP_RCHILD(op);

    int LeftLen = LIST_LENGTH(lChild->schema->attrDefs);

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


	/*
	 * WHERE provenance dependencies (Definition 1).
	 *
	 * Keep the original Selection above the join for query semantics.  Do not
	 * push/copy the predicate into the table-access branches.  Instead,
	 * recursively collect every referenced source attribute and send only that
	 * dependency information to the appropriate child.
	 *
	 * This handles:
	 *   - one condition,
	 *   - arbitrarily many AND/OR conditions,
	 *   - nested predicates,
	 *   - seller-only WHERE attributes that are not in SELECT.
	 *
	 * It also removes the old duplicate-filter behavior where the same WHERE
	 * predicate could be evaluated both below and above the join.
	 */
	if(HAS_STRING_PROP(op, PROP_WHERE_CLAUSE))
	{
		Node *whereCond = GET_STRING_PROP(op, PROP_WHERE_CLAUSE);
		int rightLen = LIST_LENGTH(rChild->schema->attrDefs);

		List *leftWhereAttrs =
		        igCollectWhereAttrsForSide(
		                whereCond,
		                lChild,
		                0,
		                LeftLen);

		List *rightWhereAttrs =
		        igCollectWhereAttrsForSide(
		                whereCond,
		                rChild,
		                LeftLen,
		                rightLen);

		if(leftWhereAttrs != NIL)
			SET_STRING_PROP(
			        lChild,
			        IG_WHERE_ATTRS_PROP,
			        copyObject(leftWhereAttrs));

		if(rightWhereAttrs != NIL)
			SET_STRING_PROP(
			        rChild,
			        IG_WHERE_ATTRS_PROP,
			        copyObject(rightWhereAttrs));

		DEBUG_LOG(
		        "P-XDV WHERE dependencies: left=%d right=%d",
		        LIST_LENGTH(leftWhereAttrs),
		        LIST_LENGTH(rightWhereAttrs));
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

    /*
     * Resolve join-condition references by source side + local position before
     * generated unique output names are used by later P-XDV stages.
     */
    igNormalizeJoinCondRefsBySide(op, lChild, rChild);

    makeAttrNamesUnique((QueryOperator *) op);

    /*
     * Preserve the full JOIN condition tree. Downstream code can recursively
     * obtain all referenced attributes with getAttrReferences(), so there is
     * no single-vs-multiple-condition special case.
     */
    SET_STRING_PROP(
            op,
            PROP_JOIN_ATTRS_FOR_HAMMING,
            singleton(copyObject(op->cond)));


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
	Constant *joinType = (Constant *) GET_STRING_PROP((QueryOperator *) op, IG_JOIN_TYPE);

    /*
     * Source attributes referenced by WHERE.  Join rewrites populate this
     * property with side-local references.  For a direct Selection over a
     * single table, derive the same dependency list locally.
     */
    List *whereAttrs = NIL;

    if(HAS_STRING_PROP((QueryOperator *) op, IG_WHERE_ATTRS_PROP))
    {
        whereAttrs = copyObject(
                GET_STRING_PROP(
                        (QueryOperator *) op,
                        IG_WHERE_ATTRS_PROP));
    }
    else if(HAS_STRING_PROP((QueryOperator *) op, PROP_WHERE_CLAUSE))
    {
        Node *whereCond =
                GET_STRING_PROP(
                        (QueryOperator *) op,
                        PROP_WHERE_CLAUSE);

        whereAttrs =
                igCollectWhereAttrsForSide(
                        whereCond,
                        (QueryOperator *) op,
                        0,
                        LIST_LENGTH(op->op.schema->attrDefs));
    }

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

	/*
	 * Recursively collect CASE dependencies.
	 *
	 * caseCondAttrs contains all source attributes used anywhere in WHEN
	 * predicates. thenElseAttrs contains all source attributes used anywhere
	 * in THEN and ELSE result expressions.
	 */
	List *caseCondAttrs = NIL;
	List *thenElseAttrs = NIL;

	FOREACH(Node, inputExpr, input_attrs)
	{
		if(!isA(inputExpr, CaseExpr))
			continue;

		CaseExpr *ce = (CaseExpr *) inputExpr;

		FOREACH(CaseWhen, cw, ce->whenClauses)
		{
            List *whenRefs = getAttrReferences(cw->when);

            FOREACH(AttributeReference, caseAr, whenRefs)
            {
                if(searchArList(caseCondAttrs, caseAr->name) == 0)
                    caseCondAttrs =
                            appendToTailOfList(caseCondAttrs, caseAr);
            }

            List *thenRefs = getAttrReferences(cw->then);

            FOREACH(AttributeReference, resultAr, thenRefs)
            {
                if(searchArList(thenElseAttrs, resultAr->name) == 0)
                    thenElseAttrs =
                            appendToTailOfList(thenElseAttrs, resultAr);
            }
		}

        List *elseRefs = getAttrReferences(ce->elseRes);

        FOREACH(AttributeReference, resultAr, elseRefs)
        {
            if(searchArList(thenElseAttrs, resultAr->name) == 0)
                thenElseAttrs =
                        appendToTailOfList(thenElseAttrs, resultAr);
        }
	}

	FOREACH(AttributeReference, ar , thenElseAttrs)
	{
    	if(isSuffix(ar->name,"1"))
    	{
    		ar->name = replaceSubstr(ar->name,"1","");
    	}
	}

	FOREACH(AttributeReference, ar, caseCondAttrs)
	{
	    if(isSuffix(ar->name, "1"))
	    {
	        ar->name = replaceSubstr(ar->name, "1", "");
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

		/*
		 * BUG FIX:
		 * Add right-side attributes that occur only inside CASE WHEN conditions.
		 *
		 * Example:
		 *      CASE WHEN (... b.gdays <= 70) THEN ... ELSE ...
		 *
		 * b.gdays is not in the SELECT list, but it affects the output quality.
		 * Therefore it must be captured as a right-side DG/provenance attribute.
		 */
		FOREACH(AttributeReference, ar, caseCondAttrs)
		{
		    if(ar->attrPosition >= left_len
		            && searchArList(joinattrs, ar->name) == 0
		            && searchArList(newProjExpr, ar->name) == 0)
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

    /*
     * Definition 1: an attribute used only in WHERE is still query-relevant.
     * Add each side-local WHERE dependency to the conversion/DG helper set.
     * Deduplicate by source attribute name so an attribute used in SELECT,
     * CASE, and WHERE still gets exactly one helper.
     */
    FOREACH(AttributeReference, whereAr, whereAttrs)
    {
        int sourcePos =
                getAttrPos(
                        (QueryOperator *) op,
                        whereAr->name);

        if(sourcePos >= 0
                && searchArList(newProjExpr, whereAr->name) == 0)
        {
            AttributeDef *sourceDef =
                    getAttrDefByPos(
                            (QueryOperator *) op,
                            sourcePos);

            if(sourceDef != NULL)
            {
                newProjExpr =
                        appendToTailOfList(
                                newProjExpr,
                                createFullAttrReference(
                                        sourceDef->attrName,
                                        0,
                                        sourcePos,
                                        0,
                                        sourceDef->dataType));

                newProjNames =
                        appendToTailOfList(
                                newProjNames,
                                strdup(sourceDef->attrName));
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

    /*
     * Do not materialize another Selection here.  rewriteIG_Selection keeps
     * the original WHERE operator above the rewritten child, so evaluating it
     * again at TableAccess would duplicate the filter and is unsafe for outer
     * joins / complex predicates.
     */
    addChildOperator((QueryOperator *) po, (QueryOperator *) op);
    switchSubtrees((QueryOperator *) op, (QueryOperator *) po);

    tablePos = tablePos + 1; // to change 0 from 1
    DEBUG_LOG("table access after adding additional attributes for ig: %s", operatorToOverviewString((Node *) po));
    return rewriteIG_Conversion(po);
}

