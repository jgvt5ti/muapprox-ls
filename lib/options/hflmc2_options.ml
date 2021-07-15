[@@@ocaml.warning "-39"]

open Hflmc2_util

(******************************************************************************)
(* Options                                                                    *)
(******************************************************************************)

let format = ref (Obj.magic())
let timeout = ref (Obj.magic())
let print_for_debug = ref (Obj.magic())
let no_backend_inlining = ref (Obj.magic())
let no_separate_original_formula_in_exists = ref (Obj.magic())
let solver = ref (Obj.magic())
let solver_backend = ref (Obj.magic())
let first_order_solver = ref (Obj.magic())
let coe = ref (Obj.magic())
let dry_run = ref (Obj.magic())
let no_simplify = ref (Obj.magic())
let stop_on_unknown = ref (Obj.magic())
let always_approximate = ref (Obj.magic())
let assign_values_for_exists_at_first_iteration = ref (Obj.magic())
let default_lexicographic_order = ref (Obj.magic())
let simplify_bound = ref (Obj.magic())
let use_simple_encoding_when_lexico_is_one = ref (Obj.magic())
let disable_lexicographic = ref (Obj.magic())
let add_arguments = ref (Obj.magic())
let coe_arguments = ref (Obj.magic())
let no_elim = ref (Obj.magic())
let eliminate_unused_arguments = ref (Obj.magic()) 
let partial_analysis = ref (Obj.magic ())
let use_related = ref (Obj.magic ())
let use_all_variables = ref (Obj.magic())
(******************************************************************************)
(* Parser                                                                     *)
(******************************************************************************)

let set_ref ref x = ref := x

type params =
  {
  input : string list [@pos 0] [@docv "FILE"]
  (** input file path *)
  
  ; format : string [@default "auto"]
  (** input file format ("auto" / "hes" / "in". Default is "auto") *)

  ; no_inlining_backend : bool [@default false]
  (** Disable inlining in a backend solver *)
  
  ; timeout : float [@default 240.0]
  (** Timeout for a backend solver *)
  
  ; print_for_debug : bool [@default true]
  (** Print for debug *)
  
  ; no_separate_original_formula_in_exists : bool [@default true]
  (** If specified, when approximating exists, do not create new predicate that reduces the formula size *)
  
  ; solver : string [@default "katsura"]
  (** Choose background nu-only-HFLz solver. Available: katsura, iwayama, suzuki *)
  
  ; solver_backend : string [@default ""]
  (** --solver option on the backend solver. (only used in the katsura solver) *)
  
  ; first_order_solver : bool [@default false]
  (** If true, use z3 or hoice to solve first-order formulas. If empty (or default), always use a solver for higher-order formulas. *)
  
  ; coe : string [@default "1,1"]
  (** Initial coefficients for approximating mu and exists. Speficfy such as "1,8" (default is "1,1") *)
  
  ; dry_run : bool [@default false]
  (** Do not solve *)
  
  ; no_simplify : bool [@default false]
  (** Do not simplify formula. It seems to get better results when false. (default: false) *)
  
  ; stop_on_unknown : bool [@default false]
  (** If false, skip "Unknown" result from a backend solver (the same behaviour as "Invalid" result). If true, stop solving when get "Unknown". (default: false) *)
  
  ; always_approximate : bool [@default false]
  (** Always approximate a HFLz formula even if the formula (or its dual) is v-HFLz. (debug purpose) *)
  
  ; instantiate_exists: bool [@defalut false]
  (** At the first iteration (coe1=1, coe2=1), assign concrete values to existentially quantified variables. *)
  
  ; default_lexicographic_order: int [@default 1]
  (** Default number of pairs when using lexicographic order *)
  
  ; simplify_bound : bool [@default false]
  (** Simplify bound formulas for approximating mu *)
  
  ; use_simple_encoding_when_lexico_is_one: bool [@default true]
  (** Use simple encoding when lexicographic order is one *)
  
  ; disable_lexicographic: bool [@default false]
  (** Disable trying encoding of lexicographic order *)
  
  ; add_arguments : bool [@default false]
  (** Add integer arguments that represent information of higher-order arguments *)
  
  ; coe_arguments : string [@default "1,0"]
  (** Coefficients of added arguments (default: 1,0) *)
  
  ; no_elim : bool [@default false]
  (** Don't eliminate mu and exists (debug purpose) *)
  
  ; partial_analysis : bool [@default false]
  (** Analyze partial applications to optimize added arguments *)
  
  ; use_related : bool [@default false]
  (** Analyze related integer variables to optimize added arguments *)
  
  ; use_all_variables : bool [@default false]
  (** Use all variables (not only variables which are occured in arguments of application) to guess a recursion bound to approximate least-fixpoints. (This may (or may not) help Hoice.) *)
  
  ; eliminate_unused_arguments : bool [@default false]
  (** Eliminate unused arguments using type-based analysis *)
  }
[@@deriving cmdliner,show]

let set_up_params params =
  set_ref format                   params.format;
  set_ref timeout                  params.timeout;
  set_ref print_for_debug          params.print_for_debug;
  set_ref no_separate_original_formula_in_exists params.no_separate_original_formula_in_exists;
  set_ref no_backend_inlining      params.no_inlining_backend;
  set_ref solver                   params.solver;
  set_ref solver_backend           params.solver_backend;
  set_ref first_order_solver       params.first_order_solver;
  set_ref coe                      params.coe;
  set_ref dry_run                  params.dry_run;
  set_ref no_simplify              params.no_simplify;
  set_ref stop_on_unknown           params.stop_on_unknown;
  set_ref always_approximate       params.always_approximate;
  set_ref assign_values_for_exists_at_first_iteration params.instantiate_exists;
  set_ref default_lexicographic_order params.default_lexicographic_order;
  set_ref simplify_bound       params.simplify_bound;
  set_ref use_simple_encoding_when_lexico_is_one params.use_simple_encoding_when_lexico_is_one;
  set_ref disable_lexicographic params.disable_lexicographic;
  set_ref add_arguments params.add_arguments;
  set_ref coe_arguments params.coe_arguments;
  set_ref no_elim params.no_elim;
  set_ref eliminate_unused_arguments params.eliminate_unused_arguments;
  set_ref partial_analysis params.partial_analysis;
  set_ref use_related params.use_related;
  set_ref use_all_variables params.use_all_variables;
  params.input

(******************************************************************************)
(* Term                                                                       *)
(******************************************************************************)

let term_set_up_params () =
  Cmdliner.Term.(const set_up_params $ params_cmdliner_term ())

module Logs     = Logs
module Logs_cli = Logs_cli
module Logs_fmt = Logs_fmt

(* Log *)
let term_setup_log () =
  (*{{{*)
  let setup style_renderer level =
    Format.set_margin 1000;
    Fmt_tty.setup_std_outputs ?style_renderer ();
    let pp_header ppf (src, level, header) =
      let src_str =
        if Logs.Src.(equal src Logs.default)
        then None
        else Some (Logs.Src.name src)
      in
      let level_str, style = match (level : Logs.level) with
        | App     -> "App"     , Logs_fmt.app_style
        | Error   -> "Error"   , Logs_fmt.err_style
        | Warning -> "Warning" , Logs_fmt.warn_style
        | Info    -> "Info"    , Logs_fmt.info_style
        | Debug   -> "Debug"   , Logs_fmt.debug_style
      in
      let (<+) x y = match x with None -> y | Some x -> x ^ ":" ^ y in
      let (+>) x y = match y with None -> x | Some y -> x ^ ":" ^ y in
      let str = src_str <+ level_str +> header in
      Fmt.pf ppf "@[<v 2>[%a]@ @]" Fmt.(styled style string) str
    in
    let reporter =
      { Logs.report = fun src level ~over k msgf ->
          let k _ = over (); k () in
          msgf @@ fun ?header ?tags:_ fmt ->
            let ppf = Fmt.stdout in
            Format.kfprintf k ppf ("%a@[" ^^ fmt ^^ "@]@.")
              pp_header (src, level, header)
      }
    in
    Logs.set_reporter reporter;
    Logs.set_level level
  in
    Cmdliner.Term.(const setup $ Fmt_cli.style_renderer () $ Logs_cli.level ())
(*}}}*)

type input = [`File of string | `Stdin]
let parse ?argv () : input option =
  let term () =
    let open Cmdliner.Term in
    const (fun _ file -> file)
      $ term_setup_log () (* NOTE order matters *)
      $ term_set_up_params ()
  in match Cmdliner.Term.(eval ?argv (term (), info "muapprox")) with
  | `Ok [] -> Some `Stdin
  | `Ok [file] -> Some (`File file)
  | `Ok _ -> Fn.todo ~info:"multiple input files" ()
  | _     -> None

