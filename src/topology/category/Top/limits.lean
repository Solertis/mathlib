/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import topology.category.Top.basic
import category_theory.limits.types
import category_theory.limits.preserves.basic

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

open topological_space
open category_theory
open category_theory.limits
open opposite

universes u v

noncomputable theory

namespace Top

variables {J : Type u} [small_category J]

local notation `forget` := forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨(types.limit_cone (F ⋙ forget)).X, ⨅j,
        (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
  π :=
  { app := λ j, ⟨(types.limit_cone (F ⋙ forget)).π.app j,
                 continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f,
                   continuous_map.coe_inj ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone F) :=
by { refine is_limit.of_faithful forget (types.limit_cone_is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.π.app j).continuous :
         _) ) }

instance Top_has_limits : has_limits.{u} Top.{u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) } }

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨(types.colimit_cocone (F ⋙ forget)).X, ⨆ j,
        (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
  ι :=
  { app := λ j, ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j,
                 continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f,
                   continuous_map.coe_inj ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit_cocone F) :=
by { refine is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (λ s, ⟨_, _⟩)
       (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.ι.app j).continuous :
         _) ) }

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk { cocone := colimit_cocone F, is_colimit :=
    colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

end Top

namespace Top

section topological_konig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)
-/

variables {J : Type u} [directed_order J]
variables (F : Jᵒᵖ ⥤ Top.{u})

/--
The partial sections of an inverse system of topological spaces from an index `j` are sections
when restricted to all objects less than or equal to `j`.
-/
def partial_sections (j : Jᵒᵖ) : set (Π j, F.obj j) :=
{ u | ∀ {j'} (f : j ⟶ j'), F.map f (u j) = u j'}

lemma partial_sections.nonempty [Π (j : Jᵒᵖ), nonempty (F.obj j)] (j : Jᵒᵖ) :
  (partial_sections F j).nonempty :=
begin
  classical,
  use λ (j' : Jᵒᵖ),
    if h : j'.unop ≤ j.unop then
      F.map (hom_of_le h).op (classical.arbitrary (F.obj j))
    else
      classical.arbitrary _,
  intros j' fle,
  simp only [dif_pos (le_of_hom fle.unop)],
  dsimp, simp,
end

lemma partial_sections.directed : directed (⊇) (partial_sections F) :=
begin
  intros j j',
  obtain ⟨j'', hj''⟩ := directed_order.directed j.unop j'.unop,
  use op j'',
  split,
  { intros u hu j''' f''',
    rw [←hu ((hom_of_le hj''.1).op ≫ f'''), ←hu],
    simp only [Top.comp_app, functor.map_comp] },
  { intros u hu j''' f''',
    rw [←hu ((hom_of_le hj''.2).op ≫ f'''), ←hu],
    simp only [Top.comp_app, functor.map_comp] },
end

lemma partial_sections.closed [Π (j : Jᵒᵖ), t2_space (F.obj j)] (j : Jᵒᵖ) :
  is_closed (partial_sections F j) :=
begin
  have hps : partial_sections F j =
    ⋂ (f : Σ j', j ⟶ j'), {u : Π (j : Jᵒᵖ), F.obj j | F.map f.2 (u j) = u f.1},
  { ext u,
    simp only [set.mem_Inter, sigma.forall, set.mem_set_of_eq],
    exact ⟨λ hu j' f, hu f, λ hu j' f, hu j' f⟩ },
  rw hps,
  apply is_closed_Inter,
  rintros ⟨j', f⟩,
  let proj : Π (j' : Jᵒᵖ), C((Π (j : Jᵒᵖ), F.obj j), F.obj j') :=
    λ j', ⟨λ u, u j', continuous_apply j'⟩,
  exact is_closed_eq
    (((F.map f).continuous.comp (proj j).continuous).comp continuous_id)
    ((proj j').continuous.comp continuous_id),
end

lemma nonempty_limit_cone_of_compact_t2_inverse_system
  [Π (j : Jᵒᵖ), nonempty (F.obj j)]
  [Π (j : Jᵒᵖ), compact_space (F.obj j)]
  [Π (j : Jᵒᵖ), t2_space (F.obj j)] :
  nonempty (Top.limit_cone F).X :=
begin
  by_cases h : nonempty Jᵒᵖ,
  { haveI := h,
    obtain ⟨u, hu⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
      (partial_sections F) (partial_sections.directed F) (partial_sections.nonempty F)
      (λ j, is_closed.compact (partial_sections.closed F j)) (partial_sections.closed F),
    use u,
    intros j j' f,
    specialize hu (partial_sections F j),
    simp only [forall_prop_of_true, set.mem_range_self] at hu,
    exact hu f, },
  { exact ⟨⟨λ j, (h ⟨j⟩).elim, λ j, (h ⟨j⟩).elim⟩⟩, },
end

end topological_konig

end Top

section fintype_konig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe. -/
lemma nonempty_sections_of_fintype_inverse_system.init
  {J : Type u} [directed_order J] (F : Jᵒᵖ ⥤ Type u)
  [hf : Π (j : Jᵒᵖ), fintype (F.obj j)] [hne : Π (j : Jᵒᵖ), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  let F' : Jᵒᵖ ⥤ Top := F ⋙ Top.discrete,
  haveI : Π (j : Jᵒᵖ), fintype (F'.obj j) := hf,
  haveI : Π (j : Jᵒᵖ), nonempty (F'.obj j) := hne,
  obtain ⟨⟨u, hu⟩⟩ := Top.nonempty_limit_cone_of_compact_t2_inverse_system F',
  exact ⟨u, λ j j' f, hu f⟩,
end

/-- Gives the induced directed order on the `ulift` of a type with a directed order. -/
def ulift.directed_order {α : Type u} [directed_order α] : directed_order (ulift.{v} α) :=
{ le := λ i j, i.down ≤ j.down,
  le_refl := λ i, le_refl i.down,
  le_trans := λ i j k hij hjk, le_trans hij hjk,
  directed := λ i j, begin
    obtain ⟨k, hk⟩ := directed_order.directed i.down j.down,
    exact ⟨ulift.up k, hk⟩,
  end }
local attribute [instance] ulift.directed_order

/-- The inverse limit of nonempty finite types is nonempty.  This may be regarded
as a generalization of Kőnig's lemma. -/
theorem nonempty_sections_of_fintype_inverse_system
  {J : Type u} [directed_order J] (F : Jᵒᵖ ⥤ Type v)
  [Π (j : Jᵒᵖ), fintype (F.obj j)] [Π (j : Jᵒᵖ), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  let J' := ulift.{v} J,
  letI : small_category J' := by apply_instance,
  let jj : J' ⥤ J :=
  { obj := λ i, i.down,
    map := λ i j f, hom_of_le (le_of_hom f : i ≤ j) },
  let F' : J'ᵒᵖ ⥤ Type (max u v) := (jj.op ⋙ F ⋙ ulift_functor : J'ᵒᵖ ⥤ Type (max v u)),
  haveI : ∀ i, nonempty (F'.obj i) := λ i,
    ⟨ulift.up (classical.arbitrary (F.obj (op i.unop.down)))⟩,
  haveI : ∀ i, fintype (F'.obj i) := λ i,
    fintype.of_equiv (F.obj (op i.unop.down))
    { to_fun := λ x, ulift.up x,
      inv_fun := λ x, x.down,
      left_inv := by tidy,
      right_inv := by tidy, },
  obtain ⟨u, hu⟩ := nonempty_sections_of_fintype_inverse_system.init F',
  refine ⟨λ j, (u (op $ ulift.up j.unop)).down, _⟩,
  intros j j' f,
  let f' : op (ulift.up.{v} j.unop) ⟶ op (ulift.up.{v} j'.unop),
  { refine (hom_of_le _).op, exact (le_of_hom f.unop : unop j' ≤ unop j), },
  have h := hu f',
  simp only [functor.comp_map, functor.op_map, ulift_functor_map] at h,
  simp only [←h], dsimp,
  rw hom_of_le_le_of_hom,
  refl,
end

end fintype_konig
