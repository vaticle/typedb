grammar GraqlTemplate;

template
 : block EOF
 ;

block
 : (filler | statement)+
 ;

statement
 : forStatement
 | nullableStatement
 | noescpStatement
 ;

forStatement
 : LPAREN FOR identifier IN identifier RPAREN LBRACKET block RBRACKET
 ;

nullableStatement
 : NULLABLE
 ;

noescpStatement
 : NOESCP
 ;

filler      : (WORD | identifier)+;
identifier  : IDENTIFIER;

// reserved
FOR         : 'for' ;
IN          : 'in' ;
NULLABLE    : 'nullable' ;
NOESCP      : 'noescp' ;

IDENTIFIER  : '%' [a-zA-Z0-9_-]+;
LPAREN      : '(';
RPAREN      : ')';
LBRACKET    : '{';
RBRACKET    : '}';
WORD        : (~([ \t\r\n])+);

WS : [ \t\r\n]+ -> channel(HIDDEN) ;
