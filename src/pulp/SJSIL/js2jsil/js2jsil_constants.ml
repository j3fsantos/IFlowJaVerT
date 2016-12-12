
let js2jsil_imports = [
	"Array";
	"Boolean";
	"Date";
	"Function";
	"Global";
	"Init";
	"Internals";
	"Math";
	"Number";
	"Object";
	"RegExp";
	"String";
	"Errors"
]

let js2jsil_logic_imports = [
	"obj_int_fun"; "js_preds"
]

let setupHeapName = "setupInitialHeap"

let callPropName              = "@call"
let constructPropName         = "@construct"
let scopePropName             = "@scope"
let classPropName             = "@class"
let extensiblePropName        = "@extensible"
let internalProtoFieldName    = "@proto"

let locGlobName        = "$lg"
let locObjPrototype    = "$lobj_proto"
let locArrPrototype    = "$larr_proto"

let toBooleanName                     = "i__toBoolean"                   (* 9.2               *)
let getValueName                      = "i__getValue"                    (* 8.7.1             *)
let isReservedName                    = "i__isReserved"
let putValueName                      = "i__putValue"                    (* 8.7.2             *)
let createDefaultObjectName           = "create_default_object"          (* 15.2.2.1          *)
let toObjectName                      = "i__toObject"                    (* 9.9               *)
let toStringName                      = "i__toString"                    (* 9.8               *)
let deletePropertyName                = "deleteProperty"                 (* 8.12.7            *)
let syntaxErrorName                   = "SyntaxError"                    (* 15.1.4.13         *)
let typeErrorName                     = "TypeError"                      (* 15.1.4.14         *)
let createFunctionObjectName          = "create_function_object"
let isCallableName                    = "i__isCallable"
let copyObjectName                    = "copy_object"
let checkObjectCoercibleName          = "i__checkObjectCoercible"
let jsTypeOfName                      = "i__typeOf"                      (* 11.4.3 - Table 20 *)
let toNumberName                      = "i__toNumber"                    (* 9.3 - Table 12    *)
let toPrimitiveName                   = "i__toPrimitive"                 (* 9.1 - Table 10    *)
let toInt32Name                       = "i__toInt32"                     (* 9.5               *)
let toUInt32Name                      = "i__toUint32"                    (* 9.6               *)
let abstractComparisonName            = "i__abstractComparison"          (* 11.8.5            *)
let hasPropertyName                   = "hasProperty"                    (* 8.12.6            *)
let abstractEqualityComparisonName    = "i__abstractEquality"            (* 11.9.3            *)
let strictEqualityComparisonName      = "i__strictEquality"              (* 11.9.6            *)
let defineOwnPropertyName             = "defineOwnProperty"              (* 8.12.9            *)
let checkAssignmentErrorsName         = "i__checkAssignmentErrors"
let checkParametersName               = "i__checkParameters"
let getEnumFieldsName                 = "i__getAllEnumerableFields"
let createArgsName                    = "create_arguments_object"

let var_this = "x__this"
let var_scope = "x__scope"
let var_se = "x__se"
let var_te = "x__te"
let var_er = "x__er"
