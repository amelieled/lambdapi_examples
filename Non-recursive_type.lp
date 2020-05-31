require open amelie.lambdapi_examples.Notation

// Inductive route : Type :=
// | departementale : route
// | nationale : route
// | autoroute : route.
constant symbol route          : Set
definition R ≔ τ route
constant symbol departementale : R
constant symbol nationale      : R
constant symbol autoroute      : R

// Definition agrandir (r : route) :=
//   match r with
//  | departementale => nationale
//  | nationale => autoroute
//  | autoroute => autoroute
//  end.
symbol agrandir : R → R
rule agrandir departementale ↪ nationale
 with agrandir nationale      ↪ autoroute
 with agrandir autoroute      ↪ autoroute

// Eval compute in (agrandir (agrandir nationale)).
compute agrandir (agrandir nationale)

theorem agrandir_test : // version théorème
  π (agrandir (agrandir nationale) = autoroute)
proof
  reflexivity
qed

//Inductive terrain : Type :=
//| t_terre : terrain
//| t_route : route -> terrain
//| t_batiment : terrain.
constant symbol terrain    : Set
definition Ter ≔ τ terrain
constant symbol t_terre    : Ter
constant symbol t_route    : R → Ter
constant symbol t_batiment : Ter

//Check (t_route nationale).
type t_route nationale
