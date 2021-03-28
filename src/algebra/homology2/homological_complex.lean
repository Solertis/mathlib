import algebra.homology2.complex_shape
import category_theory.limits.shapes.zero
import category_theory.subobject.lattice
import category_theory.subobject.factor_thru

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

structure homological_complex (c : complex_shape ι) :=
(X : ι → V)
(d : Π i j, X i ⟶ X j)
(shape' : ∀ i j, ¬ c.r i j → d i j = 0 . obviously)
(d_comp_d' : ∀ i j k, d i j ≫ d j k = 0 . obviously)

restate_axiom homological_complex.shape'
restate_axiom homological_complex.d_comp_d'

attribute [simp] homological_complex.shape
attribute [simp, reassoc] homological_complex.d_comp_d

namespace homological_complex
variables {V} {c : complex_shape ι} (C : homological_complex V c)

@[ext] structure hom (A B : homological_complex V c) :=
(f : ∀ i, A.X i ⟶ B.X i)
(comm' : ∀ i j, f i ≫ B.d i j = A.d i j ≫ f j . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

@[simps] def id (A : homological_complex V c) : hom A A :=
{ f := λ _, 𝟙 _ }

@[simps] def comp (A B C : homological_complex V c) (φ : hom A B) (ψ : hom B C) : hom A C :=
{ f := λ i, φ.f i ≫ ψ.f i }

instance : category (homological_complex V c) :=
{ hom := hom,
  id := id,
  comp := comp, }

open_locale classical
noncomputable theory

variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

lemma d_comp_eq_to_hom {i j j' : ι} (rij : c.r i j) (rij' : c.r i j') :
  C.d i j' ≫ eq_to_hom (congr_arg C.X (c.succ_eq rij' rij)) = C.d i j :=
begin
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

lemma eq_to_hom_comp_d {i i' j : ι} (rij : c.r i j) (rij' : c.r i' j) :
  eq_to_hom (congr_arg C.X (c.pred_eq rij rij')) ≫ C.d i' j = C.d i j :=
begin
  have P : ∀ h : i = i', eq_to_hom (congr_arg C.X h) ≫ C.d i' j = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

lemma kernel_eq_kernel [has_kernels V] {i j j' : ι} (r : c.r i j) (r' : c.r i j') :
  kernel_subobject (C.d i j) = kernel_subobject (C.d i j') :=
begin
  rw ←d_comp_eq_to_hom C r r',
  apply kernel_subobject_comp_iso,
end

lemma image_eq_image [has_images V] [has_equalizers V] [has_zero_object V]
  {i i' j : ι} (r : c.r i j) (r' : c.r i' j) :
  image_subobject (C.d i j) = image_subobject (C.d i' j) :=
begin
  rw ←eq_to_hom_comp_d C r r',
  apply image_subobject_iso_comp,
end

def X_pred (j : ι) : V :=
if h : nonempty (c.pred j) then
  C.X h.some.1
else
  0

def X_pred_iso {i j : ι} (r : c.r i j) :
  C.X_pred j ≅ C.X i :=
begin
  dsimp [X_pred],
  apply eq_to_iso,
  rw [dif_pos (c.nonempty_pred r)],
  exact congr_arg C.X (c.nonempty_pred_some r),
end

def X_pred_iso_zero {j : ι} (h : c.pred j → false) :
  C.X_pred j ≅ 0 :=
begin
  dsimp [X_pred],
  apply eq_to_iso,
  rw [dif_neg (not_nonempty_iff_imp_false.mpr h)],
end

def X_succ (i : ι) : V :=
if h : nonempty (c.succ i) then
  C.X h.some.1
else
  0

def X_succ_iso {i j : ι} (r : c.r i j) :
  C.X_succ i ≅ C.X j :=
begin
  dsimp [X_succ],
  apply eq_to_iso,
  rw [dif_pos (c.nonempty_succ r)],
  exact congr_arg C.X (c.nonempty_succ_some r),
end

def X_succ_iso_zero {i : ι} (h : c.succ i → false) :
  C.X_succ i ≅ 0 :=
begin
  dsimp [X_succ],
  apply eq_to_iso,
  rw [dif_neg (not_nonempty_iff_imp_false.mpr h)],
end

/--
The differential mapping into `C.X j`, or zero if there isn't one.
-/
def d_to (j : ι) : C.X_pred j ⟶ C.X j :=
if h : nonempty (c.pred j) then
  (C.X_pred_iso h.some.2).hom ≫ C.d h.some.1 j
else
  (0 : C.X_pred j ⟶ C.X j)

/--
The differential mapping out of `C.X i`, or zero if there isn't one.
-/
def d_from (i : ι) : C.X i ⟶ C.X_succ i :=
if h : nonempty (c.succ i) then
  C.d i h.some.1 ≫ (C.X_succ_iso h.some.2).inv
else
  (0 : C.X i ⟶ C.X_succ i)

lemma d_to_eq {i j : ι} (r : c.r i j) :
  C.d_to j = (C.X_pred_iso r).hom ≫ C.d i j :=
begin
  dsimp [d_to, X_pred_iso],
  rw [dif_pos (c.nonempty_pred r), ←is_iso.inv_comp_eq, inv_eq_to_hom, eq_to_hom_trans_assoc],
  rw C.eq_to_hom_comp_d r _,
  apply c.r_of_nonempty_pred,
end

lemma d_to_eq_zero {j : ι} (h : c.pred j → false) :
  C.d_to j = 0 :=
begin
  dsimp [d_to],
  rw [dif_neg (not_nonempty_iff_imp_false.mpr h)]
end

lemma d_from_eq {i j : ι} (r : c.r i j) :
  C.d_from i = C.d i j ≫ (C.X_succ_iso r).inv :=
begin
  dsimp [d_from, X_succ_iso],
  rw [dif_pos (c.nonempty_succ r), ←is_iso.comp_inv_eq, inv_eq_to_hom, category.assoc,
    eq_to_hom_trans],
  rw C.d_comp_eq_to_hom r _,
  apply c.r_of_nonempty_succ,
end

lemma d_from_eq_zero {i : ι} (h : c.succ i → false) :
  C.d_from i = 0 :=
begin
  dsimp [d_from],
  rw [dif_neg (not_nonempty_iff_imp_false.mpr h)]
end

@[simp]
lemma d_to_comp_d_from (j : ι) : C.d_to j ≫ C.d_from j = 0 :=
begin
  by_cases h : nonempty (c.pred j),
  { obtain ⟨⟨i, rij⟩⟩ := h,
    by_cases h' : nonempty (c.succ j),
    { obtain ⟨⟨k, rjk⟩⟩ := h',
      rw [C.d_to_eq rij, C.d_from_eq rjk],
      simp, },
    { rw [C.d_from_eq_zero (not_nonempty_iff_imp_false.mp h')],
      simp, }, },
  { rw [C.d_to_eq_zero (not_nonempty_iff_imp_false.mp h)],
    simp, },
end

lemma kernel_from_eq_kernel [has_kernels V] {i j : ι} (r : c.r i j) :
  kernel_subobject (C.d_from i) = kernel_subobject (C.d i j) :=
begin
  rw C.d_from_eq r,
  apply kernel_subobject_comp_iso,
end

lemma image_to_eq_image [has_images V] [has_equalizers V] [has_zero_object V]
  {i j : ι} (r : c.r i j) :
  image_subobject (C.d_to j) = image_subobject (C.d i j) :=
begin
  rw C.d_to_eq r,
  apply image_subobject_iso_comp,
end

/-! Lemmas relating chain maps and `d_to`/`d_from`. -/
namespace hom

variables {C₁ C₂ : homological_complex V c}

def f_pred (f : hom C₁ C₂) (i : ι) : C₁.X_pred i ⟶ C₂.X_pred i :=
if h : nonempty (c.pred i) then
  (C₁.X_pred_iso h.some.2).hom ≫ f.f h.some.1 ≫ (C₂.X_pred_iso h.some.2).inv
else
  0

def f_succ (f : hom C₁ C₂) (i : ι) : C₁.X_succ i ⟶ C₂.X_succ i :=
if h : nonempty (c.succ i) then
  (C₁.X_succ_iso h.some.2).hom ≫ f.f h.some.1 ≫ (C₂.X_succ_iso h.some.2).inv
else
  0

@[simp, reassoc]
def comm_d_from (f : C₁ ⟶ C₂) (i : ι) :
  f.f i ≫ C₂.d_from i = C₁.d_from i ≫ f.f_succ i :=
begin
  dsimp [d_from, f_succ],
  split_ifs; simp
end

end hom

end homological_complex