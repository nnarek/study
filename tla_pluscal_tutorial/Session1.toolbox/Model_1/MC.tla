---- MODULE MC ----
EXTENDS Session1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_174240608369723000 == 
IsPrime(79)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_174240608369723000>>)
----

=============================================================================
\* Modification History
\* Created Wed Mar 19 21:41:23 GET 2025 by developer
