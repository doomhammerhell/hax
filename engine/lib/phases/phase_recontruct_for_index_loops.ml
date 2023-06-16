open Base
open Utils

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.On.For_index_loop
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ResugarForIndexLoops
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id

      let for_index_loop = Fn.const Features.On.for_index_loop
    end

    [%%inline_defs dmutability]

    let rec dloop_kind (span : span) (k : A.loop_kind) : B.loop_kind =
      match k with
      | ForLoop
          {
            it =
              {
                e =
                  App
                    {
                      f = { e = GlobalVar (`Concrete into_iter_meth) };
                      args =
                        [
                          {
                            e =
                              Construct
                                {
                                  constructor = `Concrete range_ctor;
                                  constructs_record = true;
                                  fields =
                                    [
                                      (`Concrete start_field, start);
                                      (`Concrete end_field, end_);
                                    ];
                                  base = None;
                                };
                          };
                        ];
                    };
                typ;
                _;
              };
            pat =
              {
                p =
                  PBinding
                    { mut = Immutable; mode = ByValue; var; subpat = None };
                typ = _;
              };
            witness;
          }
        when Concrete_ident.eq_name
               Core__iter__traits__collect__IntoIterator__into_iter
               into_iter_meth
             && Concrete_ident.eq_name Core__ops__range__Range__start
                  start_field
             && Concrete_ident.eq_name Core__ops__range__Range range_ctor
             && Concrete_ident.eq_name Core__ops__range__Range__end end_field ->
          ForIndexLoop
            {
              start = dexpr start;
              end_ = dexpr end_;
              var;
              var_typ = dty span typ;
              witness = Features.On.for_index_loop;
            }
      | [%inline_arms "dloop_kind.*"] -> auto
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]
