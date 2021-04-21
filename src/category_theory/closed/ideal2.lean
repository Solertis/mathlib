/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.shapes.binary_products
import category_theory.monad.limits
import category_theory.adjunction.fully_faithful
import category_theory.adjunction.reflective
import category_theory.closed.cartesian
import category_theory.subterminal

/-!
# Exponential ideals

An exponential ideal of a cartesian closed category `C` is a subcategory `D ⊆ C` if for any `B : D`
and `A : C`, the exponential `B^^A` is in `D` - resembling ring theoretic ideals. We define the
notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories.

We give alternate conditions for an exponential ideal, particularly when the subcategory is
reflective.

-/
universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open limits category

section ideal

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D] {i : D ⥤ C}

variables (i) [has_finite_products C] [cartesian_closed C]

/--
The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `B^A ∈ D` for all `A`.
-/
class exponential_ideal : Prop :=
(exp_closed : ∀ {B}, B ∈ i.ess_image → ∀ A, (A ⟹ B) ∈ i.ess_image)

/--
To show `i` is an exponential ideal it suffices to show that `(iB)^A` is `in` `D` for any `A` in `C`
and `B` in `D`.
-/
lemma exponential_ideal.mk' (h : ∀ (B : D) (A : C), (A ⟹ i.obj B) ∈ i.ess_image) :
  exponential_ideal i :=
⟨λ B hB A,
begin
  rcases hB with ⟨B', ⟨iB'⟩⟩,
  exact functor.ess_image.of_iso ((exp A).map_iso iB') (h B' A),
end⟩

/-- The subcategory of subterminal objects is an exponential ideal. -/
instance : exponential_ideal (subterminal_inclusion C) :=
begin
  apply exponential_ideal.mk',
  intros B A,
  refine ⟨⟨B.1 ^^ A, λ Z g h, _⟩, ⟨iso.refl _⟩⟩,
  exact uncurry_injective (B.2 (cartesian_closed.uncurry g) (cartesian_closed.uncurry h))
end

/--
If `D` is a reflective subcategory, the property of being an exponential ideal is equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A`, that is:
`(iB)^A ≅ i L (iB)^A`, naturally in `B`.
The converse is given in `exponential_ideal.mk_of_iso`.
-/
def exponential_ideal_reflective (A : C) [reflective i] [exponential_ideal i] :
  i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A :=
begin
  symmetry,
  apply nat_iso.of_components _ _,
  { intro X,
    haveI := (exponential_ideal.exp_closed (i.obj_mem_ess_image X) A).unit_is_iso,
    apply as_iso ((adjunction.of_right_adjoint i).unit.app (i.obj X ^^ A)) },
  { simp }
end

/--
Given a natural isomorphism `i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A`, we can show `i`
is an exponential ideal.
-/
lemma exponential_ideal.mk_of_iso [reflective i]
  (h : Π (A : C), i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A) :
  exponential_ideal i :=
begin
  apply exponential_ideal.mk',
  intros B A,
  exact ⟨_, ⟨(h A).app B⟩⟩,
end

end ideal

section

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D]
variables (i : D ⥤ C) [has_finite_products C] [reflective i]

lemma reflective_products [reflective i] : has_finite_products D :=
⟨λ J 𝒥₁ 𝒥₂, by exactI has_limits_of_shape_of_reflective i⟩

local attribute [instance, priority 10] reflective_products

variables [cartesian_closed C]

/--
If the reflector preserves binary products, the subcategory is an exponential ideal.
This is the converse of `preserves_binary_products_of_exponential_ideal`.
-/
instance exponential_ideal_of_preserves_binary_products
  [preserves_limits_of_shape (discrete walking_pair) (left_adjoint i)] :
  exponential_ideal i :=
begin
  let ir := adjunction.of_right_adjoint i,
  let L : C ⥤ D := left_adjoint i,
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit,
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit,
  apply exponential_ideal.mk',
  intros B A,
  let q : i.obj (L.obj (i.obj B ^^ A)) ⟶ i.obj B ^^ A,
    apply cartesian_closed.curry (ir.hom_equiv _ _ _),
    apply _ ≫ (ir.hom_equiv _ _).symm ((ev A).app (i.obj B)),
    refine prod_comparison L A _ ≫ limits.prod.map (𝟙 _) (ε.app _) ≫ inv (prod_comparison _ _ _),
  have : η.app (i.obj B ^^ A) ≫ q = 𝟙 (i.obj B ^^ A),
  { dsimp,
    rw [← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev, ← ir.hom_equiv_naturality_left,
        ir.hom_equiv_apply_eq, assoc, assoc, prod_comparison_natural_assoc, L.map_id,
        ← prod.map_id_comp_assoc, ir.left_triangle_components, prod.map_id_id, id_comp],
    apply is_iso.hom_inv_id_assoc },
  haveI : split_mono (η.app (i.obj B ^^ A)) := ⟨_, this⟩,
  apply mem_ess_image_of_unit_split_mono,
end

variables [exponential_ideal i]

/--
If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself cartesian closed.
-/
def reflective_cc : cartesian_closed D :=
{ closed := λ B,
  { is_adj :=
    { right := i ⋙ exp (i.obj B) ⋙ left_adjoint i,
      adj :=
      begin
        apply adjunction.restrict_fully_faithful i i (exp.adjunction (i.obj B)),
        { symmetry,
          apply nat_iso.of_components _ _,
          { intro X,
            haveI := adjunction.right_adjoint_preserves_limits (adjunction.of_right_adjoint i),
            apply as_iso (prod_comparison i B X) },
          { intros X Y f,
            dsimp,
            rw prod_comparison_natural,
            simp, } },
        { apply (exponential_ideal_reflective i _).symm }
      end } } }

-- It's annoying that I need to do this.
local attribute [-instance] category_theory.preserves_limit_of_creates_limit_and_has_limit
local attribute [-instance] category_theory.preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape

/--
We construct a bijection between morphisms `L(A ⨯ B) ⟶ X` and morphisms `LA ⨯ LB ⟶ X`.
This bijection has two key properties:
* It is natural in `X`: See `bijection_natural`.
* When `X = LA ⨯ LB`, then the backwards direction sends the identity morphism to the product
  comparison morphism: See `bijection_symm_apply_id`.

Together these help show that `L` preserves binary products.
-/
noncomputable def bijection (A B : C) (X : D) :
  ((left_adjoint i).obj (A ⨯ B) ⟶ X) ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ X) :=
calc _ ≃ (A ⨯ B ⟶ i.obj X) :
              (adjunction.of_right_adjoint i).hom_equiv _ _
   ... ≃ (B ⨯ A ⟶ i.obj X) :
              (limits.prod.braiding _ _).hom_congr (iso.refl _)
   ... ≃ (A ⟶ B ⟹ i.obj X) :
              (exp.adjunction _).hom_equiv _ _
   ... ≃ (i.obj ((left_adjoint i).obj A) ⟶ B ⟹ i.obj X) :
              unit_comp_partial_bijective _ (exponential_ideal.exp_closed (i.obj_mem_ess_image _) _)
   ... ≃ (B ⨯ i.obj ((left_adjoint i).obj A) ⟶ i.obj X) :
              ((exp.adjunction _).hom_equiv _ _).symm
   ... ≃ (i.obj ((left_adjoint i).obj A) ⨯ B ⟶ i.obj X) :
              (limits.prod.braiding _ _).hom_congr (iso.refl _)
   ... ≃ (B ⟶ i.obj ((left_adjoint i).obj A) ⟹ i.obj X) :
              (exp.adjunction _).hom_equiv _ _
   ... ≃ (i.obj ((left_adjoint i).obj B) ⟶ i.obj ((left_adjoint i).obj A) ⟹ i.obj X) :
              unit_comp_partial_bijective _ (exponential_ideal.exp_closed (i.obj_mem_ess_image _) _)
   ... ≃ (i.obj ((left_adjoint i).obj A) ⨯ i.obj ((left_adjoint i).obj B) ⟶ i.obj X) :
              ((exp.adjunction _).hom_equiv _ _).symm
   ... ≃ (i.obj ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B) ⟶ i.obj X) :
     begin
       apply iso.hom_congr _ (iso.refl _),
       haveI : preserves_limits i := (adjunction.of_right_adjoint i).right_adjoint_preserves_limits,
       exact (preserves_pair.iso _ _ _).symm,
     end
   ... ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ X) :
              (equiv_of_fully_faithful _).symm

lemma bijection_symm_apply_id (A B : C) :
  (bijection i A B _).symm (𝟙 _) = prod_comparison _ _ _ :=
begin
  dsimp [bijection],
  rw [comp_id, comp_id, comp_id, i.map_id, comp_id, unit_comp_partial_bijective_symm_apply,
      unit_comp_partial_bijective_symm_apply, uncurry_natural_left, uncurry_curry,
      uncurry_natural_left, uncurry_curry, prod.lift_map_assoc, comp_id, prod.lift_map_assoc,
      comp_id, prod.comp_lift_assoc, prod.lift_snd, prod.lift_fst_assoc,
      prod.lift_fst_comp_snd_comp, ←adjunction.eq_hom_equiv_apply, adjunction.hom_equiv_unit,
      iso.comp_inv_eq, assoc, preserves_pair.iso_hom],
  apply prod.hom_ext,
  { rw [limits.prod.map_fst, assoc, assoc, prod_comparison_fst, ←i.map_comp, prod_comparison_fst],
    apply (adjunction.of_right_adjoint i).unit.naturality },
  { rw [limits.prod.map_snd, assoc, assoc, prod_comparison_snd, ←i.map_comp, prod_comparison_snd],
    apply (adjunction.of_right_adjoint i).unit.naturality },
end

lemma bijection_natural [reflective i] [exponential_ideal i]
  (A B : C) (X X' : D) (f : ((left_adjoint i).obj (A ⨯ B) ⟶ X)) (g : X ⟶ X') :
  bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g :=
begin
  dsimp [bijection],
  apply i.map_injective,
  rw [i.image_preimage, i.map_comp, i.image_preimage, comp_id, comp_id, comp_id, comp_id, comp_id,
      comp_id, adjunction.hom_equiv_naturality_right, ← assoc, curry_natural_right _ (i.map g),
      unit_comp_partial_bijective_natural, uncurry_natural_right, ← assoc, curry_natural_right,
      unit_comp_partial_bijective_natural, uncurry_natural_right, assoc],
end

/--
The bijection allows us to show that `prod_comparison L A B` is an isomorphism, where the inverse
is the forward map of the identity morphism.
-/
def prod_comparison_iso (A B : C) :
  is_iso (prod_comparison (left_adjoint i) A B) :=
⟨⟨bijection i _ _ _ (𝟙 _),
  by rw [←(bijection i _ _ _).injective.eq_iff, bijection_natural, ← bijection_symm_apply_id,
         equiv.apply_symm_apply, id_comp],
  by rw [←bijection_natural, id_comp, ←bijection_symm_apply_id, equiv.apply_symm_apply]⟩⟩

local attribute [instance] prod_comparison_iso

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves binary products.
This is the converse of `exponential_ideal_of_preserves_binary_products`.
-/
-- TODO: Show that the reflector also preserves the terminal object and hence that it preserves
-- finite products.
noncomputable def preserves_binary_products_of_exponential_ideal :
  preserves_limits_of_shape (discrete walking_pair) (left_adjoint i) :=
{ preserves_limit := λ K,
  begin
    apply limits.preserves_limit_of_iso_diagram _ (diagram_iso_pair K).symm,
    apply preserves_pair.of_iso_comparison,
  end }

end

end category_theory
