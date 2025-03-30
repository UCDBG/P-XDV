/*
 *
 * A FILE FOR IG FUNCTIONS SO IN THIS CASE
 *
 */

#include "provenance_rewriter/ig_rewrites/ig_main.h"
#include "configuration/option.h"
#include "instrumentation/timing_instrumentation.h"
#include "provenance_rewriter/pi_cs_rewrites/pi_cs_main.h"
#include "provenance_rewriter/ig_rewrites/ig_main.h"
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

#define IG_PREFIX "ig_"

// creates a list of attribute references from a list of attributeDefs with no given positions
extern List *getARfromAttrDefs(List *qo);
extern List *getNamesfromAttrDefs(List *qo);
extern List *getARfromAttrDefswPos(QueryOperator *qo, List *attrDefs);
extern char *getTableNamefromPo(ProjectionOperator *po);
extern List *getARfromPoAr(ProjectionOperator *po);
extern List *getNamesfromPoAr(ProjectionOperator *po);

extern int searchArList(List *arList, char *ch);
extern int searchAdefList(List *adefList, char *ch);

extern List *removeDupeAr(List *arList);
extern int searchArListByPos(List *arList, int pos);

extern QueryOperator *cleanEXPL(QueryOperator *qo);


//Input : AttributeReference (Data Type : DT_STRING)
//Pitput : array of Ascii codes of string (Data Type : DT_INT)
extern Ascii *convertArtoAscii(AttributeReference *ar);

//Input : ProjectionOperator
//Output : List of converted AttributeReference toAscii and rest of the attributes
extern List *toAsciiList(ProjectionOperator *po);

//Input : List of projection expressions(contains Ascii, AttributeReference, CastExpr)
extern List *getAsciiAggrs(List *projExprs);

AttributeReference *getAttrRefFromArListByPos(List* arList, int pos);

extern int searchArListForPos(List *arList, char *ch);

extern int searchCasePosinArList(List *arList);

extern int hasAscii(List *arList);


int searchCasePosinArList(List *arList)
{
	int pos = 0;
	FOREACH(AttributeReference, ar, arList)
	{
		if(isA(ar, CaseExpr))
		{
			return pos;
		}
		else
		{
			pos = pos + 1;
		}
	}

	return -1; // case when not found
}

int hasAscii(List *arList)
{
	FOREACH(AttributeReference, ar, arList)
	{
		if(isA(ar, Ascii))
		{
			return 1;
		}
	}
	return 0; // 0 = FALSE, not found
}

int searchArListForPos(List *arList, char *ch)
{
	FOREACH(AttributeReference, ar, arList)
	{
		if(streq(ar->name, ch))
		{
			return ar->attrPosition;
		}
	}
	return -1; // -1 = attribute no
}


AttributeReference *getAttrRefFromArListByPos(List* arList, int pos)
{
	FOREACH(AttributeReference, ar, arList)
	{
		if(ar->attrPosition == pos)
		{
			return ar;
		}
	}
	return NULL;
}

int searchArListByPos(List *arList, int pos)
{
	FOREACH(AttributeReference, ar, arList)
	{
		if(ar->attrPosition == pos)
		{
			return 1; // 1 = TRUE
		}
	}
		return 0; // 0 = FALSE
}


List *removeDupeAr(List *arList)
{
	List *cleanArList = NIL;
	FOREACH(AttributeReference, ar, arList)
	{
		if(searchArListByPos(cleanArList, ar->attrPosition) == 0)
		{
			cleanArList = appendToTailOfList(cleanArList, ar);
		}
	}

	return cleanArList;
}

// this function does not check for case when, only attribute reference
int searchArList(List *arList, char *ch)
{
	FOREACH(AttributeReference, ar, arList)
	{
		if(isA(ar, AttributeReference))
		{
			if(strcmp(ar->name, ch) == 0)
			{
				return 1; // 1 = TRUE
				break;
			}
		}
	}
	return 0; // 0 = FALSE
}

int searchAdefList(List *adefList, char *ch)
{
	FOREACH(AttributeDef, adef, adefList)
	{
		if(strcmp(adef->attrName, ch))
		{
			return 1; // 1 = TRUE
			break;
		}
	}
	return 0; // 0 = FALSE
}

QueryOperator *cleanEXPL(QueryOperator *qo)
{

	List *cleanExprs = NIL;
	List *cleanNames = NIL;

	List *valueR2 = NIL;
	List *valueR2Names = NIL;

	FOREACH(AttributeDef, a, qo->schema->attrDefs)
	{

		if(streq(a->attrName, "fscoreTopK") || streq(a->attrName, "f_score"))
		{
			continue;
		}
		else if(isSuffix(a->attrName, "r2") && isPrefix(a->attrName, "ig"))
		{
			continue;
		}
		else if(isSuffix(a->attrName, "r2") && isPrefix(a->attrName, "value"))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
					getAttrPos(qo, a->attrName), 0, a->dataType);
			valueR2 = appendToTailOfList(valueR2, ar);
			valueR2Names = appendToTailOfList(valueR2Names, a->attrName);
		}
		else
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
					getAttrPos(qo, a->attrName), 0, a->dataType);
			cleanExprs = appendToTailOfList(cleanExprs, ar);
			cleanNames = appendToTailOfList(cleanNames, a->attrName);
		}
	}

//	ProjectionOperator *cleanpo = createProjectionOp(CONCAT_LISTS(cleanExprs,valueR2),
//			qo, NIL, CONCAT_LISTS(cleanNames,valueR2Names));

	ProjectionOperator *cleanpo = createProjectionOp(cleanExprs, qo, NIL, cleanNames);

	addParent(qo, (QueryOperator *) cleanpo);
	switchSubtrees(qo, (QueryOperator *) cleanpo);

	return (QueryOperator *) cleanpo;


}




//rewrite conversion functions

Ascii *convertArtoAscii(AttributeReference *a)
{
	StringToArray *toArray;
	Unnest *tounnest;
	Ascii *toAscii;

	if (a->attrType == DT_STRING)
	{
		toArray = createStringToArrayExpr((Node *) a, "NULL");
		tounnest = createUnnestExpr((Node *) toArray);
		toAscii = createAsciiExpr((Node *) tounnest);
	}
	else
	{
		// invalid input : ERROR
		return NULL;
	}

	return toAscii;
}

List *toAsciiList(ProjectionOperator *op)
{
	List *projExprs = NIL;

	//changing schema for string attributes
	FOREACH(AttributeDef, adef, op->op.schema->attrDefs)
	{
		if(isPrefix(adef->attrName, "ig") && adef->dataType == DT_STRING)
		{
			adef->dataType = DT_INT;
		}
	}

	FOREACH(AttributeReference, a, op->projExprs)
	{
		if(isPrefix(a->name, "ig") && a->attrType == DT_STRING)
		{
			if (a->attrType == DT_STRING)
			{
				Ascii *toAscii = convertArtoAscii(a);
				projExprs = appendToTailOfList(projExprs, toAscii);
			}
			else
			{
				projExprs = appendToTailOfList(projExprs, a);
			}
		}
		else
		{
			projExprs = appendToTailOfList(projExprs, a);
		}
	}

	return projExprs;
}


List *getAsciiAggrs(List *projExprs)
{
	List *aggrs = NIL;
	FOREACH(AttributeReference, n, projExprs)
	{
		if(isA(n,Ascii))
		{
			Ascii *ai = (Ascii *) n;
			Unnest *un = (Unnest *) ai->expr;
			StringToArray *sta = (StringToArray *) un->expr;
			AttributeReference *ar = (AttributeReference *) sta->expr;
			ar->attrType = DT_INT;
			FunctionCall *sum = createFunctionCall("SUM", singleton(ar));
			aggrs = appendToTailOfList(aggrs,sum);
		}
	}
	return aggrs;
}

// creates a list of attribute references from a list of attributeDefs with no given positions
List *getARfromAttrDefs(List *attrDefs)
{
	List *projExprs = NIL;
	int pos = 0;

	FOREACH(AttributeDef, a, attrDefs)
	{

		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0, pos, 0, a->dataType));

		pos++;
	}

	return projExprs;
}

// creates a list of attribute references from a list of attributeDefs with given positions form an expression
List *getARfromAttrDefswPos(QueryOperator *qo, List *attrDefs)
{
	List *projExprs = NIL;

	FOREACH(AttributeDef, a, attrDefs)
	{
		projExprs = appendToTailOfList(projExprs,
			createFullAttrReference(a->attrName, 0,
					getAttrPos(qo, a->attrName), 0,
					isPrefix(a->attrName,"ig") ? DT_BIT10 : a->dataType));

	}

	return projExprs;
}


List *getNamesfromAttrDefs(List *attrDefs)
{
	List *projNames = NIL;
	FOREACH(AttributeDef, a, attrDefs)
	{
		projNames = appendToTailOfList(projNames, a->attrName);
	}

	return projNames;
}

char *getTableNamefromPo(ProjectionOperator *po)
{
	char *tableName = NULL;
	FOREACH(AttributeReference, n, po->projExprs)
	{
		if(isPrefix(n->name, IG_PREFIX))
		{
			int len1 = strlen(n->name);
			int len2 = strlen(strrchr(n->name, '_'));
			int len = len1 - len2 - 1;
			tableName = substr(n->name, 8, len);
		}
	}
	return tableName;
}

List *getARfromPoAr(ProjectionOperator *po)
{
	List *projExprs = NIL;
	FOREACH(AttributeReference, n, po->projExprs)
	{
		projExprs = appendToTailOfList(projExprs, n);
	}
	return projExprs;
}

List *getNamesfromPoAr(ProjectionOperator *po)
{
	List *projNames = NIL;
	FOREACH(AttributeReference, n, po->projExprs)
	{
		projNames = appendToTailOfList(projNames, n->name);
	}
	return projNames;
}



