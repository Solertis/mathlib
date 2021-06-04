/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import measure_theory.interval_integral
import order.filter.at_top_bot

open measure_theory filter set topological_space
open_locale ennreal nnreal topological_space

namespace measure_theory

section ae_cover

variables {α ι : Type*} [preorder ι]
  [measurable_space α] (μ : measure α)

/-- A sequence `φ` of subsets of `α` is a `ae_cover` w.r.t. a measure `μ`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n`, and if
    each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `+∞`.

    See for example `measure_theory.set_lintegral_tendsto_lintegral`,
    `measure_theory.integrable_of_set_integral_norm_tendsto` and
    `measure_theory.set_integral_tendsto_integral`. -/
structure ae_cover (φ : ι → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in at_top, x ∈ φ i)
(measurable : ∀ i, measurable_set $ φ i)

variables {μ}

section preorder

variables [preorder α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a at_top at_bot) (hb : tendsto b at_top at_top)

lemma ae_cover_Icc :
  ae_cover μ (λ i, Icc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Icc }

lemma ae_cover_Ici :
  ae_cover μ (λ i, Ici $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ici }

lemma ae_cover_Iic :
  ae_cover μ (λ i, Iic $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iic }

end preorder

section linear_order

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a at_top at_bot) (hb : tendsto b at_top at_top)

lemma ae_cover_Ioo [no_bot_order α] [no_top_order α] :
  ae_cover μ (λ i, Ioo (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioo }

lemma ae_cover_Ioc [no_bot_order α] : ae_cover μ (λ i, Ioc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioc }

lemma ae_cover_Ico [no_top_order α] : ae_cover μ (λ i, Ico (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ico }

lemma ae_cover_Ioi [no_bot_order α] :
  ae_cover μ (λ i, Ioi $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ioi }

lemma ae_cover_Iio [no_top_order α] :
  ae_cover μ (λ i, Iio $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iio }

end linear_order

lemma ae_cover.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β]
  {f : α → β} {φ : ι → set α} (hφ : ae_cover μ φ) :
  ∀ᵐ x ∂μ, tendsto (λ i, (φ i).indicator f x) at_top (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

end ae_cover

lemma ae_cover.comp_tendsto_at_top {α ι ι' : Type*} [semilattice_sup ι] [nonempty ι]
  [preorder ι'] [measurable_space α] {μ : measure α} {φ : ι → set α} (hφ : ae_cover μ φ)
  {u : ι' → ι} (hu : tendsto u at_top at_top) :
  ae_cover μ (φ ∘ u) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
  begin
    intros x hx,
    rw eventually_at_top at hx,
    rcases hx with ⟨i, hi⟩,
    exact (hu.eventually (eventually_ge_at_top i)).mono (λ j hij, hi (u j) hij)
  end,
  measurable := λ i, hφ.measurable (u i) }

section ae_cover_Union_Inter_encodable

section preorder_ι

variables {α ι : Type*} [preorder ι] [encodable ι]
  [measurable_space α] {μ : measure α}

lemma ae_cover.bUnion_Iic_ae_cover {φ : ι → set α} (hφ : ae_cover μ φ) :
  ae_cover μ (λ (n : ι), ⋃ k (h : k ∈ Iic n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    (λ x h, h.mono (λ i hi, mem_bUnion right_mem_Iic hi)),
  measurable := λ i, measurable_set.bUnion (countable_encodable _) (λ n _, hφ.measurable n) }

--move me
lemma bUnion_Iic_mono (φ : ι → set α) :
  monotone (λ (n : ι), ⋃ k (h : k ∈ Iic n), φ k) :=
λ i j hij, bUnion_subset_bUnion_left (λ k hk, le_trans hk hij)

--move me
lemma subset_bUnion_Iic (φ : ι → set α) (n : ι) :
  φ n ⊆ ⋃ k (h : k ∈ Iic n), φ k :=
subset_bUnion_of_mem right_mem_Iic

end preorder_ι

section linear_order_ι

variables {α ι : Type*} [linear_order ι] [encodable ι]
  [measurable_space α] {μ : measure α}

lemma ae_cover.bInter_Ici_ae_cover {φ : ι → set α} (hφ : ae_cover μ φ)
  [nonempty ι] : ae_cover μ (λ (n : ι), ⋂ k (h : k ∈ Ici n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    begin
      intros x h,
      rw eventually_at_top at *,
      rcases h with ⟨i, hi⟩,
      use i,
      intros j hj,
      exact mem_bInter (λ k hk, hi k (le_trans hj hk)),
    end,
  measurable := λ i, measurable_set.bInter (countable_encodable _) (λ n _, hφ.measurable n) }

--move me
lemma bInter_Ici_mono (φ : ι → set α) :
  monotone (λ (n : ι), ⋂ k (h : k ∈ Ici n), φ k) :=
λ i j hij, bInter_subset_bInter_left (λ k hk, le_trans hij hk)

--move me
lemma bInter_Ici_subset (φ : ι → set α) (n : ι) :
  (⋂ k (h : k ∈ Ici n), φ k) ⊆ φ n :=
bInter_subset_of_mem left_mem_Ici

end linear_order_ι

end ae_cover_Union_Inter_encodable

section lintegral

variables {α ι : Type*} [measurable_space α] {μ : measure α} [semilattice_sup ι] [nonempty ι]

lemma ae_cover.lintegral_tendsto_of_monotone_of_nat {φ : ℕ → set α} (hφ : ae_cover μ φ)
  (hmono : monotone φ) {f : α → ℝ≥0∞} (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
let F := λ n, (φ n).indicator f in
have key₁ : ∀ n, ae_measurable (F n) μ, from λ n, (hfm.indicator (hφ.measurable n)).ae_measurable,
have key₂ : ∀ᵐ (x : α) ∂μ, monotone (λ n, F n x), from ae_of_all _
  (λ x i j hij, indicator_le_indicator_of_subset (hmono hij) (λ x, zero_le $ f x) x),
have key₃ : ∀ᵐ (x : α) ∂μ, tendsto (λ n, F n x) at_top (𝓝 (f x)), from hφ.ae_tendsto_indicator,
(lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr
  (λ n, lintegral_indicator f (hφ.measurable n))

lemma ae_cover.lintegral_tendsto_of_nat {φ : ℕ → set α} (hφ : ae_cover μ φ)
  {f : α → ℝ≥0∞} (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
begin
  have lim₁ := hφ.bInter_Ici_ae_cover.lintegral_tendsto_of_monotone_of_nat (bInter_Ici_mono φ) hfm,
  have lim₂ := hφ.bUnion_Iic_ae_cover.lintegral_tendsto_of_monotone_of_nat (bUnion_Iic_mono φ) hfm,
  have le₁ := λ n, lintegral_mono_set (bInter_Ici_subset φ n),
  have le₂ := λ n, lintegral_mono_set (subset_bUnion_Iic φ n),
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ le₁ le₂
end

lemma ae_cover.lintegral_tendsto_of_at_top_countably_generated {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → ℝ≥0∞} (hfm : measurable f) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
htop.tendsto_of_seq_tendsto (λ u hu, (hφ.comp_tendsto_at_top hu).lintegral_tendsto_of_nat hfm)

-- TODO : change name to `set_...` ?

lemma ae_cover.lintegral_eq_of_tendsto {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → ℝ≥0∞} (I : ℝ≥0∞)
  (hfm : measurable f) (htendsto : tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
tendsto_nhds_unique (hφ.lintegral_tendsto_of_at_top_countably_generated htop hfm) htendsto

lemma ae_cover.supr_lintegral_eq_of_at_top_countably_generated {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → ℝ≥0∞} (hfm : measurable f) :
  (⨆ (i : ι), ∫⁻ x in φ i, f x ∂μ) = ∫⁻ x, f x ∂μ :=
begin
  have := hφ.lintegral_tendsto_of_at_top_countably_generated htop hfm,
  refine csupr_eq_of_forall_le_of_forall_lt_exists_gt
    (λ i, lintegral_mono' measure.restrict_le_self (le_refl _)) (λ w hw, _),
  rcases exists_between hw with ⟨m, hm₁, hm₂⟩,
  rcases (eventually_ge_of_tendsto_gt hm₂ this).exists with ⟨i, hi⟩,
  exact ⟨i, lt_of_lt_of_le hm₁ hi⟩,
end

end lintegral

section integrable

variables {α ι E : Type*} [semilattice_sup ι] [nonempty ι]
  [measurable_space α] {μ : measure α} [normed_group E]
  [measurable_space E] [opens_measurable_space E]

lemma ae_cover.integrable_of_lintegral_nnnorm_tendsto {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → E} (I : ℝ) (hfm : measurable f)
  (htendsto : tendsto (λ i, ∫⁻ x in φ i, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine ⟨hfm.ae_measurable, _⟩,
  unfold has_finite_integral,
  rw hφ.lintegral_eq_of_tendsto htop _
    (measurable_ennreal_coe_iff.mpr (measurable_nnnorm.comp hfm)) htendsto,
  exact ennreal.of_real_lt_top
end

lemma ae_cover.integrable_of_lintegral_nnorm_tendsto' {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → E} (I : ℝ≥0) (hfm : measurable f)
  (htendsto : tendsto (λ i, ∫⁻ x in φ i, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
hφ.integrable_of_lintegral_nnnorm_tendsto htop (I : ℝ) hfm htendsto

lemma ae_cover.integrable_of_integral_norm_tendsto {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → E}
  (I : ℝ) (hfm : measurable f) (hfi : ∀ i, integrable_on f (φ i) μ)
  (htendsto : tendsto (λ i, ∫ x in φ i, ∥f x∥ ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  refine hφ.integrable_of_lintegral_nnnorm_tendsto htop I hfm _,
  conv at htendsto in (integral _ _)
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg E _ (f x)))
    hfm.norm.ae_measurable },
  conv at htendsto in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  convert ennreal.tendsto_of_real htendsto,
  ext i : 1,
  rw ennreal.of_real_to_real _,
  exact ne_top_of_lt (hfi i).2
end

-- TODO : of_nonneg

end integrable

section integral

variables {α ι E : Type*} [semilattice_sup ι] [nonempty ι]
  [measurable_space α] {μ : measure α} [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E] [second_countable_topology E]

lemma ae_cover.integral_tendsto_of_at_top_countably_generated {φ : ι → set α} (hφ : ae_cover μ φ)
  (htop : (at_top : filter ι).is_countably_generated) {f : α → E} (hfm : measurable f)
  (hfi : integrable f μ) :
  tendsto (λ i, ∫ x in φ i, f x ∂μ) at_top (𝓝 $ ∫ x, f x ∂μ) :=
suffices h : tendsto (λ i, ∫ (x : α), (φ i).indicator f x ∂μ) at_top (𝓝 (∫ (x : α), f x ∂μ)),
by {convert h,
    ext n,
    rw integral_indicator (hφ.measurable n)},
tendsto_integral_filter_of_dominated_convergence (λ x, ∥f x∥) htop
  (eventually_of_forall $ λ i, (hfm.indicator $ hφ.measurable i).ae_measurable) hfm.ae_measurable
  (eventually_of_forall $ λ i, ae_of_all _ $ λ x, norm_indicator_le_norm_self _ _)
  hfi.norm hφ.ae_tendsto_indicator

-- TODO : of_nonneg

end integral

section integrable_of_interval_integral

variables {α ι E : Type*}
          [semilattice_sup ι] [nonempty ι]
          [topological_space α] [linear_order α] [order_closed_topology α]
          [measurable_space α] [opens_measurable_space α] {μ : measure α}
          [measurable_space E] [normed_group E] [borel_space E]
          (htop : (at_top : filter ι).is_countably_generated)
          {a b : ι → α} {f : α → E} (hfm : measurable f)

include htop hfm

lemma integrable_of_interval_integral_norm_tendsto [no_bot_order α] [nonempty α]
  (I : ℝ) (hfi : ∀ i, integrable_on f (Ioc (a i) (b i)) μ)
  (ha : tendsto a at_top at_bot) (hb : tendsto b at_top at_top)
  (h : tendsto (λ i, ∫ x in a i .. b i, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable f μ :=
begin
  let φ := λ n, Ioc (a n) (b n),
  let c : α := classical.choice ‹_›,
  have hφ : ae_cover μ φ := ae_cover_Ioc ha hb,
  refine hφ.integrable_of_integral_norm_tendsto htop _ hfm hfi (h.congr' _),
  filter_upwards [ha.eventually (eventually_le_at_bot c), hb.eventually (eventually_ge_at_top c)],
  intros i hai hbi,
  exact interval_integral.integral_of_le (hai.trans hbi)
end

lemma integrable_on_Iic_of_interval_integral_norm_tendsto [no_bot_order α] (I : ℝ) (b : α)
  (hfi : ∀ i, integrable_on f (Ioc (a i) b) μ) (ha : tendsto a at_top at_bot)
  (h : tendsto (λ i, ∫ x in a i .. b, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable_on f (Iic b) μ :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : ae_cover (μ.restrict $ Iic b) φ := ae_cover_Ioi ha,
  have hfi : ∀ i, integrable_on f (φ i) (μ.restrict $ Iic b),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i)],
    exact hfi i },
  refine hφ.integrable_of_integral_norm_tendsto htop _ hfm hfi (h.congr' _),
  filter_upwards [ha.eventually (eventually_le_at_bot b)],
  intros i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl
end

lemma integrable_on_Ioi_of_interval_integral_norm_tendsto (I : ℝ) (a : α)
  (hfi : ∀ i, integrable_on f (Ioc a (b i)) μ) (hb : tendsto b at_top at_top)
  (h : tendsto (λ i, ∫ x in a .. b i, ∥f x∥ ∂μ) at_top (𝓝 $ I)) :
  integrable_on f (Ioi a) μ :=
begin
  let φ := λ i, Iic (b i),
  have hφ : ae_cover (μ.restrict $ Ioi a) φ := ae_cover_Iic hb,
  have hfi : ∀ i, integrable_on f (φ i) (μ.restrict $ Ioi a),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i), inter_comm],
    exact hfi i },
  refine hφ.integrable_of_integral_norm_tendsto htop _ hfm hfi (h.congr' _),
  filter_upwards [hb.eventually (eventually_ge_at_top $ a)],
  intros i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl
end

end integrable_of_interval_integral

section integral_of_interval_integral

variables {α ι E : Type*}
          [semilattice_sup ι] [nonempty ι]
          [topological_space α] [linear_order α] [order_closed_topology α]
          [measurable_space α] [opens_measurable_space α] {μ : measure α}
          [measurable_space E] [normed_group E] [normed_space ℝ E] [borel_space E]
          [complete_space E] [second_countable_topology E]
          (htop : (at_top : filter ι).is_countably_generated)
          {a b : ι → α} {f : α → E} (hfm : measurable f)

include htop hfm

lemma interval_integral_tendsto_integral [no_bot_order α] [nonempty α]
  (hfi : integrable f μ) (ha : tendsto a at_top at_bot) (hb : tendsto b at_top at_top) :
  tendsto (λ i, ∫ x in a i .. b i, f x ∂μ) at_top (𝓝 $ ∫ x, f x ∂μ) :=
begin
  let φ := λ i, Ioc (a i) (b i),
  let c : α := classical.choice ‹_›,
  have hφ : ae_cover μ φ := ae_cover_Ioc ha hb,
  refine (hφ.integral_tendsto_of_at_top_countably_generated htop hfm hfi).congr' _,
  filter_upwards [ha.eventually (eventually_le_at_bot c), hb.eventually (eventually_ge_at_top c)],
  intros i hai hbi,
  exact (interval_integral.integral_of_le (hai.trans hbi)).symm
end

lemma interval_integral_tendsto_integral_Iic [no_bot_order α] (b : α)
  (hfi : integrable_on f (Iic b) μ) (ha : tendsto a at_top at_bot) :
  tendsto (λ i, ∫ x in a i .. b, f x ∂μ) at_top (𝓝 $ ∫ x in Iic b, f x ∂μ) :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : ae_cover (μ.restrict $ Iic b) φ := ae_cover_Ioi ha,
  refine (hφ.integral_tendsto_of_at_top_countably_generated htop hfm hfi).congr' _,
  filter_upwards [ha.eventually (eventually_le_at_bot $ b)],
  intros i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl
end

lemma interval_integral_tendsto_integral_Ioi (a : α)
  (hfi : integrable_on f (Ioi a) μ) (hb : tendsto b at_top at_top) :
  tendsto (λ i, ∫ x in a .. b i, f x ∂μ) at_top (𝓝 $ ∫ x in Ioi a, f x ∂μ) :=
begin
  let φ := λ i, Iic (b i),
  have hφ : ae_cover (μ.restrict $ Ioi a) φ := ae_cover_Iic hb,
  refine (hφ.integral_tendsto_of_at_top_countably_generated htop hfm hfi).congr' _,
  filter_upwards [hb.eventually (eventually_ge_at_top $ a)],
  intros i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl
end

end integral_of_interval_integral

section examples -- will be removed later (TODO)



end examples

end measure_theory
