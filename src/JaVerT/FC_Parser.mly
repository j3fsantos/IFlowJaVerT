(***** Token definitions *****)
%token COMMA
%token <string> VAR
%token EOF

%type <string list> param_list_FC_target
%start param_list_FC_target
%%

param_list_FC_target:
	param_list = separated_list(COMMA, VAR); EOF
	{ param_list };