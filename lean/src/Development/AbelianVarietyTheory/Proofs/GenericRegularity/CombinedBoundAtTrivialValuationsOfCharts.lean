import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentre
import Formalism.LocalToGlobal.ProjectiveLattices.RegModelC
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree

noncomputable section

namespace GlobalTheory.Reg.TrivBound

open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg

alias vV_nonneg := Transfer.vV_nonneg
alias vV_unit := Transfer.vV_unit
alias mem_of_vV_nonneg := Transfer.mem_of_vV_nonneg
alias nval_nonneg := Transfer.nval_nonneg
alias nval_unit := Transfer.nval_unit
alias ne_zero_map := Transfer.ne_zero_map
alias chval_eq := Transfer.chval_eq
alias chval_div := Transfer.chval_div
alias chval_nonneg := Transfer.chval_nonneg

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]

def vr (e : ℕ) (x : V) : ℝ := (vV V (algebraMap V (FractionRing V) x) : ℝ) / e

theorem nval_eq_vr (e : ℕ) {x : V} (hx : x ≠ 0) :
    nval V e (algebraMap V (FractionRing V) x) = (vr e x : EReal) :=
  Transfer.nval_eq_vr e hx

theorem vr_mul (e : ℕ) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : vr e (x * y) = vr e x + vr e y :=
  Transfer.vr_mul e hx hy

theorem vr_one (e : ℕ) : vr e (1 : V) = 0 :=
  Transfer.vr_one e

theorem chval_fin_iff (φ : A →+* V) (e : ℕ) (f : FractionRing A) (u : ℝ) :
    ChV φ e f (u : EReal) ↔ ∃ x s : A, φ s ≠ 0 ∧ φ x ≠ 0 ∧
      f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) x ∧ u = vr e (φ x) - vr e (φ s) :=
  Transfer.chval_fin_iff φ e f u

alias chval_fin_mul := Transfer.chval_fin_mul
alias chval_fin_one := Transfer.chval_fin_one
alias chval_fin_pow := Transfer.chval_fin_pow
alias chval_fin_inv := Transfer.chval_fin_inv

theorem chval_fin_alg (φ : A →+* V) (e : ℕ) (a : A) (ha : φ a ≠ 0) :
    ChV φ e (algebraMap A (FractionRing A) a) ((vr e (φ a) : ℝ) : EReal) :=
  Transfer.chval_fin_alg φ e a ha

alias chval_fin_zpow := Transfer.chval_fin_zpow

end

alias vV_zero' := Transfer.vV_zero'
alias transfer'' := Transfer.regular_at_centre

theorem comb_core {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (ϖ : O) (eO : ℕ) (heO : 0 < eO)
    (fw fe : FractionRing A) (hfw0 : fw ≠ 0) (x : A) (hx : x ≠ 0)
    (ye : A) (hye : ye ≠ 0) (te : ℕ)
    (hfe : fe * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ te) = algebraMap A (FractionRing A) ye)
    (yw : A) (tw : ℕ)
    (hfw : fw⁻¹ * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw) = algebraMap A (FractionRing A) yw)
    (nu0 c' : ℝ) (N : ℕ) (Aexp : ℤ) (B : ℕ) (hA : (eO : ℝ) * N * nu0 ≤ Aexp) (hB : (N : ℝ) * c' ≤ B)
    (halg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V), φ x ≠ 0 → ∃ (e : ℕ) (W T : EReal), 0 < e ∧
        vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * (eO : ℤ) = e ∧
        ChV φ.toRingHom e fw W ∧ ChV φ.toRingHom e fe T ∧ 0 ≤ T ∧
        (T ≠ ⊤ → W ≤ (nu0 : EReal) + (c' : EReal) * T))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V] (φ : A →ₐ[O] V)
    (hφx : φ x ≠ 0) (hφϖ : algebraMap O V ϖ ≠ 0)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤)
    (e : ℕ) (w t : ℝ) (hW : ChV φ.toRingHom e fw (w : EReal)) (hT : ChV φ.toRingHom e fe (t : EReal)) :
    (N : ℝ) * w ≤ Aexp * vr e (algebraMap O V ϖ) + B * t :=
  Transfer.comb_core ϖ eO heO fw fe hfw0 x hx ye hye te hfe yw tw hfw nu0 c' N Aexp B hA hB halg V φ hφx hφϖ hqq e w t hW hT

alias chval_ne_bot := Transfer.chval_ne_bot
alias fin_of_ne_top := Transfer.fin_of_ne_top
alias chval_zero := Transfer.chval_zero
alias ratio_ge := Transfer.ratio_ge
alias w_fin := Transfer.w_fin
alias limit_lam := Transfer.limit_lam
alias limit_triv := Transfer.limit_triv

end GlobalTheory.Reg.TrivBound

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.TrivBound

open IsLocalRing Formalism.L2.PjFree

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem nonneg_triv {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    have hm : maximalIdeal S.O = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
    exact hcen ϖ hϖ
  obtain ⟨a', s', hs', hfs'⟩ := transfer'' (O := S.O) (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom 1 (S.ch j F) _ (hChV a n F hF) a' s' hfs' hs'

set_option maxHeartbeats 1000000 in

theorem comb_triv {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ q ∈ trivSet Xo c, q et ≠ ⊤ → (⨅ k, q (ws k)) ≤ (c' : EReal) * q et := by
  intro q hq hT
  obtain ⟨kj, hkj⟩ := hF
  obtain ⟨j, V, _, _, _, _, φ, hcen, hunit, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have heO : 0 < S.eO := S.overO.1
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hu := hunit ϖ hϖ
  have hϖ0 : algebraMap S.O V ϖ ≠ 0 := hu.ne_zero
  obtain ⟨hfw0, hrat, hinv⟩ := hkj j
  obtain ⟨yw, tw, hyw⟩ := hinv x hxE ϖ hϖ
  obtain ⟨ye, te, hye⟩ := S.reg j aE nE et het x hxE ϖ hϖ
  have hP : ∀ k : ℕ, φ ((algebraMap S.O (S.A j) ϖ * x) ^ k) ≠ 0 := fun k => by
    rw [map_pow, map_mul, AlgHom.commutes]; exact pow_ne_zero _ (mul_ne_zero hϖ0 hφx)
  have hWc := hChV aL nL (ws (kj j)) (hws _)
  have hTc := hChV aE nE et het
  obtain ⟨w, hw⟩ := w_fin hWc _ yw hyw hfw0 (hP tw)
  obtain ⟨t, ht⟩ := fin_of_ne_top hT (chval_ne_bot hTc)
  have hye0 : ye ≠ 0 := by
    rintro rfl
    rw [map_zero] at hye
    have hPK : algebraMap (S.A j) (FractionRing (S.A j)) ((algebraMap S.O (S.A j) ϖ * x) ^ te) ≠ 0 := by
      intro h0
      apply hP te
      rw [IsFractionRing.injective (S.A j) (FractionRing (S.A j)) (h0.trans (map_zero _).symm), map_zero]
    have hfe0 : S.ch j et = 0 := (mul_eq_zero.1 hye).resolve_right hPK
    rw [hfe0] at hTc
    exact hT (chval_zero hTc)
  have ht0 : 0 ≤ t := by
    have := nonneg_triv S hQ het (fun v' hv' => (hyp v' hv').1) q hq
    rw [ht] at this
    exact_mod_cast this
  have hκ : vr 1 (algebraMap S.O V ϖ) = 0 := by
    unfold vr
    rw [vV_unit _ (fun h => (IsLocalRing.mem_maximalIdeal _).1 h hu)]
    simp
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    have hm : maximalIdeal S.O = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
    exact hcen ϖ hϖ
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(N : ℝ) * c'⌉₊ : ℝ) * t := by
    intro N _
    have := comb_core ϖ S.eO heO (S.ch j (ws (kj j))) (S.ch j et) hfw0 x hx0 ye hye0 te hye yw tw hyw
      nu c' N ⌈(S.eO : ℝ) * N * nu⌉ ⌈(N : ℝ) * c'⌉₊ (Int.le_ceil _) (Nat.le_ceil _)
      (fun V' _ _ _ _ _ φ' hφ'x => by
        obtain ⟨ioV', e', hov', hϖ', v', hv', hch'⟩ := S.pts j V' φ' ⟨x, hxE, hφ'x⟩
        refine ⟨e', v' (ws (kj j)), v' et, hov'.1, hϖ' ϖ hϖ, hch' aL nL _ (hws _),
          hch' aE nE et het, (hyp v' hv').1, fun hT' => ?_⟩
        refine le_trans (le_iInf fun k => ?_) ((hyp v' hv').2 hT')
        obtain ⟨xk, hxk⟩ := hrat k
        have h2 := hch' aL nL (ws k) (hws k)
        rw [hxk] at h2
        exact ratio_ge (hch' aL nL _ (hws _)) h2)
      V φ hφx hϖ0 hqq 1 w t (hw ▸ hWc) (ht ▸ hTc)
    rw [hκ, mul_zero, zero_add] at this
    exact this
  have hlim := limit_triv w t c' ht0 hc' key
  calc (⨅ k, q (ws k)) ≤ q (ws (kj j)) := iInf_le _ _
    _ = (w : EReal) := hw
    _ ≤ ((c' * t : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hlim
    _ = (c' : EReal) * q et := by rw [ht, EReal.coe_mul]

theorem ordQ_mem_trivSet (q : QPt Xo c) : ordQ Xo c q ∈ trivSet Xo c := by
  refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
  obtain ⟨u, hu⟩ := q.triv a ha
  rw [← hu]
  exact vV_unit (u : q.T.V) (fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit)

end

end GlobalTheory.Reg.TrivBound

namespace GlobalTheory.Reg

theorem combined_bound_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → (∀ (la : HeightOneSpectrum (𝓞 c.F)) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro E _ _ _ H Dw l Xo c hS hN C hC aL nL aE nE k ws et c' hc' hws het ⟨la, nu, hyp⟩ q
  have hws' : ∀ i, ws i ∈ sec Xo c aL nL := fun i => hC _ _ (hws i)
  have het' : et ∈ sec Xo c aE nE := hC _ _ het
  obtain ⟨S, hF, hQ⟩ := (hS la).2 aL nL k ws hws' (hN la aL nL k ws hws' fun v hv => (hyp v hv).2.1)
  exact ⟨TrivBound.nonneg_triv S hQ het' (fun v hv => (hyp v hv).1) _ (TrivBound.ordQ_mem_trivSet q),
    TrivBound.comb_triv S hQ ws hF hws' het' nu c' hc' (fun v hv => ⟨(hyp v hv).1, (hyp v hv).2.2⟩) _
      (TrivBound.ordQ_mem_trivSet q)⟩

end GlobalTheory.Reg
