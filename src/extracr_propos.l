%{

%}

KEY next
ALPHA [A-Za-z]
VAR_NAME [{ALPHA}0-9]+
VAR_VAL [{ALPHA}0-9]+|0.[0-9]*|[1-9]+\.[0-9]*
CAL_OP +|-|*|/|%|!|=|>|<

%%
//匹配next类型的表达式
{KEY}\({VAR_NAME}\){CAL_OP}({VAR_NAME}|{VAR_VAL})({CAL_OP}{VAR_VAL}|{VAR_NAME})* printf("%s\n",yytext);
//匹配无next类型(待修正)
{VAR_NAME}{CAL_OP}({VAR_NAME}|{VAR_VAL})({CAL_OP}{VAR_VAL}|{VAR_NAME})* printf("%s\n",yytext);


%%
int main(int argc, char **argv)
{
  yylex()
  return 0;
}
int yywrap()
{
	return 1;
}
