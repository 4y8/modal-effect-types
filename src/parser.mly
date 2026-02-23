%token EOF

%type <unit> file 
%start file

%%

file: EOF { () };
