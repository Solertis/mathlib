/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.over
import category_theory.thin
import category_theory.limits.shapes.pullbacks
import category_theory.isomorphism_classes

/-!
## Subobjects in a category.

We define `subobject X` as the (isomorphism classes of) monomorphisms into `X`.
This is naturally a preorder.

When the ambient category has pullbacks, `subobject X` has an intersection operation,
and becomes a `semilattice_inf`.
-/

universes v u

noncomputable theory

namespace category_theory

variables {C : Type u} [category.{v} C]

/-- The category of monomorphisms into `X` is "thin", i.e. a preorder. -/
instance {X : C} (A B : { f : over X // mono f.hom }) : subsingleton (A ⟶ B) :=
begin
  fsplit,
  rintros ⟨f, _, wf⟩ ⟨g, _, wg⟩,
  dsimp at *, simp at wf wg, ext, dsimp,
  exact (@cancel_mono _ _ _ _ _ _ B.property _ _).mp (wf.trans (wg.symm)),
end

/--
We define the subobjects of `X` simply to be the isomorphism classes of monomorphisms into `X`.
See https://ncatlab.org/nlab/show/subobject

One could instead just take the monomorphisms directly: not much changes!
See https://mathoverflow.net/questions/184196/concise-definition-of-subobjects
However if we follow this route we only get a preorder, not a partial order,
which is less convenient for describing lattice properties.
-/
def subobject (X : C) := isomorphism_classes.obj (Cat.of { f : over X // mono f.hom })

namespace subobject

/-- Construct a subobject from an explicit monomorphism. -/
def mk {X Y : C} (f : X ⟶ Y) [w : mono f] : subobject Y :=
quot.mk _ ⟨over.mk f, w⟩

instance (X : C) : inhabited (subobject X) := ⟨mk (𝟙 _)⟩

/-- The underlying object of a subobject. -/
def X {X : C} (A : subobject X) : C :=
(isomorphism_classes.representative A).val.left

/-- The inclusion of a subobject into the ambient object. -/
def ι {X : C} (A : subobject X) : A.X ⟶ X :=
(isomorphism_classes.representative A).val.hom

instance {X : C} (A : subobject X) : mono (ι A) :=
(isomorphism_classes.representative A).property

/-- The underlying object of the subobject constructed from an explicit monomorphism is isomorphic
to the original source object. -/
def mk_X_iso {X Y : C} (f : X ⟶ Y) [w : mono f] : (mk f).X ≅ X :=
(over.forget Y).map_iso
  ((full_subcategory_inclusion _).map_iso
  (@isomorphism_classes.mk_representative_iso (Cat.of { f : over Y // mono f.hom }) ⟨over.mk f, w⟩))

@[simp]
lemma mk_X_iso_hom_comm {X Y : C} (f : X ⟶ Y) [w : mono f] :
  (mk_X_iso f).hom ≫ f = (mk f).ι :=
begin
  have h := ((full_subcategory_inclusion _).map_iso
    (@isomorphism_classes.mk_representative_iso (Cat.of { f : over Y // mono f.hom })
      ⟨over.mk f, w⟩)).hom.w,
  dsimp at h,
  simpa only [category.comp_id] using h,
end

@[simp]
lemma mk_X_iso_inv_comm {X Y : C} (f : X ⟶ Y) [w : mono f] :
  (mk_X_iso f).inv ≫ (mk f).ι = f :=
by simp [iso.inv_comp_eq]

/--
The preorder on subobjects of `X` is `(A,f) ≤ (B,g)`
if there exists a morphism `h : A ⟶ B` so `h ≫ g = f`.
(Such a morphism is unique if it exists; in a moment we upgrade this to a `partial_order`.)
-/
instance (X : C) : preorder (subobject X) :=
{ le := λ A B,
  nonempty (isomorphism_classes.representative A ⟶ isomorphism_classes.representative B),
  le_refl := λ A, ⟨𝟙 _⟩,
  le_trans := λ A B C, by { rintro ⟨f⟩, rintro ⟨g⟩, exact ⟨f ≫ g⟩, }, }

/--
Construct an inequality in the preorder on subobjects from an explicit morphism.
-/
lemma le_of_hom {X : C} {A B : subobject X} (f : A.X ⟶ B.X) (w : f ≫ B.ι = A.ι) : A ≤ B :=
nonempty.intro (over.hom_mk f w)

/-- Construct a morphism between the underlying objects from an inequality between subobjects. -/
def hom_of_le {X : C} {A B : subobject X} (h : A ≤ B) : A.X ⟶ B.X :=
comma_morphism.left (nonempty.some h)

@[simp]
lemma hom_of_le_comm {X : C} {A B : subobject X} (h : A ≤ B) :
  subobject.hom_of_le h ≫ B.ι = A.ι :=
begin
  have := (nonempty.some h).w,
  simp only [functor.id_map, functor.const.obj_map] at this,
  dsimp at this,
  simp only [category.comp_id] at this,
  exact this,
end

instance (X : C) : partial_order (subobject X) :=
{ le_antisymm := λ A B h₁ h₂,
  begin
    induction A,
    swap, refl,
    rcases A with ⟨⟨A, ⟨⟩, f⟩, w₁⟩,
    induction B,
    swap, refl,
    rcases B with ⟨⟨B, ⟨⟩, g⟩, w₂⟩,
    dsimp at A f w₁ B g w₂,
    resetI,
    apply quot.sound,
    fsplit,
    apply iso_of_both_ways,
    { fsplit,
      { exact (mk_X_iso f).inv ≫ hom_of_le h₁ ≫ (mk_X_iso g).hom, },
      { exact ⟨⟨rfl⟩⟩ },
      { dsimp,
        rw [category.comp_id, category.assoc, (mk_X_iso f).inv_comp_eq, category.assoc],
        erw [mk_X_iso_hom_comm, mk_X_iso_hom_comm, hom_of_le_comm], }, },
    { fsplit,
      { exact (mk_X_iso g).inv ≫ hom_of_le h₂ ≫ (mk_X_iso f).hom, },
      { exact ⟨⟨rfl⟩⟩ },
      { dsimp,
        rw [category.comp_id, category.assoc, (mk_X_iso g).inv_comp_eq, category.assoc],
        erw [mk_X_iso_hom_comm, mk_X_iso_hom_comm, hom_of_le_comm], }, },
  end,
  ..(by apply_instance : preorder (subobject X)) }

open category_theory.limits

section has_pullbacks
variables [has_pullbacks C] (W : C)

instance : has_inf (subobject W) :=
{ inf := λ A B,
  @mk _ _ _ W (@pullback.fst _ _ _ _ _ A.ι B.ι _ ≫ A.ι) (mono_comp _ _) }

local attribute [instance] mono_comp

lemma le_inf (X Y Z : subobject W) (f : X ≤ Y) (g : X ≤ Z) : X ≤ Y ⊓ Z :=
le_of_hom (pullback.lift (hom_of_le f) (hom_of_le g) (by simp) ≫ (mk_X_iso _).inv)
  (by { slice_lhs 2 3 { erw mk_X_iso_inv_comm _, }, simp })

lemma inf_le_left (X Y : subobject W) : X ⊓ Y ≤ X :=
le_of_hom ((mk_X_iso _).hom ≫ pullback.fst) (by { simp, refl, })

lemma inf_le_right (X Y : subobject W) : X ⊓ Y ≤ Y :=
le_of_hom ((mk_X_iso _).hom ≫ pullback.snd)
  (by { rw [category.assoc, ←pullback.condition], simp, refl, })

instance : semilattice_inf (subobject W) :=
{ le_inf := le_inf W,
  inf_le_left := inf_le_left W,
  inf_le_right := inf_le_right W,
  ..(by apply_instance : partial_order (subobject W)),
  ..(by apply_instance : has_inf (subobject W)) }

end has_pullbacks

end subobject

end category_theory
