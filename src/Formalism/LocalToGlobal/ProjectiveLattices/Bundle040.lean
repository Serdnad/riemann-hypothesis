module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def KappaTie (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (f : T.R j), f ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n →
    (evC hG Z f = 0 ↔ ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, rdU (T.U j T.σ₀) f (κ Z) x = 0)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def evCAlg (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z where
  toFun := evC hG Z
  map_one' := evalAt_one _ _ (genFr hG Z) (hT Z)
  map_mul' f g := evalAt_mul _ _ f g (genFr hG Z)
  map_zero' := evalAt_zero _ _ (genFr hG Z)
  map_add' f g := evalAt_add _ _ f g (genFr hG Z)
  commutes' a := by
    show evC hG Z (algebraMap c.F (Rul Xo c) a) = algebraMap c.F (Om Z) a
    rw [Algebra.algebraMap_eq_smul_one]
    show evalAt _ _ (a • (1 : Rul Xo c)) (genFr hG Z) = _
    rw [evalAt_smul, evalAt_one _ _ _ (hT Z), mul_one]

lemma evCAlg_apply (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) (f : Rul Xo c) :
    evCAlg hG hT Z f = evC hG Z f := rfl

end Gen

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

abbrev RZ : Type := Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω)

def rzMap : Rp X la N →ₐ[Kp X la N] RZ X la N Ω :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)

lemma rzMap_emb (F : X.Forms) :
    rzMap X la N Ω gF (emb X la N F) = (1 : Kp X la N) ⊗ₜ ((1 : X.Kl la) ⊗ₜ gF F) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)
      ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rfl

variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev RZs : Type := Localization.Away (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))

def lwZ : Lw X la w →+* RZs X la N Ω gF w :=
  Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)

lemma lwZ_alg (r : Rp X la N) :
    lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) r) =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF r) := by
  show (Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))
      (algebraMap (Rp X la N) (Localization.Away (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) r) = _
  exact IsLocalization.map_eq _ _

def phiZ : ↥(Frac0 X la w) →ₐ[Kp X la N] RZs X la N Ω gF w where
  toRingHom := (lwZ X la N Ω gF w).comp (Frac0 X la w).val.toRingHom
  commutes' k := by
    show lwZ X la N Ω gF w (algebraMap (Kp X la N) (Lw X la w) k) = _
    rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), lwZ_alg, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]

lemma phiZ_apply (x : ↥(Frac0 X la w)) : phiZ X la N Ω gF w x = lwZ X la N Ω gF w (x : Lw X la w) := rfl

end Rec

section Inst

variable {D : D7} {T : Top D} (j : ℕ)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (Z : Comp (T.Q.Xo j) T.Q.c)

def formsEvR : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] Om Z :=
  AddMonoidAlgebra.liftNCAlgHom (evCAlg hG hT Z) 1 (fun _ _ => Commute.all _ _)

lemma formsEvR_single (d : Deg D j) (f : T.R j) :
    formsEvR j hG hT Z (AddMonoidAlgebra.single d f) = evC hG Z f := by
  show AddMonoidAlgebra.liftNC (evCAlg hG hT Z).toRingHom.toAddMonoidHom
      ((1 : Multiplicative (Deg D j) →* Om Z) : Multiplicative (Deg D j) → Om Z) (AddMonoidAlgebra.single d f) = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp [evCAlg_apply]

end Inst

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem satDir_of (hS : ChartSaturated Xo c) {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) :
    SatDir T (letI := io.toAlgebra; C.ch.uvec) := by
  intro τ
  obtain ⟨⟨w, emb, hw, hbasis⟩, -⟩ := hS T io y C τ
  have huv := C.gen.1.2.2.2.2.2.2
  choose A hA using fun m : Fin (chD C.ch) => (hbasis (Pi.single m 1)).exists
  have hAw : (Matrix.of A) * (Matrix.of w) = 1 := by
    ext m j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hA m j, Pi.single_apply]
    by_cases hjm : j = m
    · subst hjm; simp
    · simp [hjm, Ne.symm hjm]
  have hwA : (Matrix.of w) * (Matrix.of A) = 1 := by
    first
      | exact mul_eq_one_comm.mp hAw
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAw
  refine ⟨fun i j => A j (emb i), fun i i' => ?_⟩
  letI := io.toAlgebra
  have e1 : ∀ j, C.ch.uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (A j (emb i)) =
      algebraMap T.V T.Fr (w (emb i') j * A j (emb i)) := by
    intro j
    rw [huv, map_mul, hw]
  refine (Finset.sum_congr rfl (fun j _ => e1 j)).trans ?_

  rw [← map_sum]
  have h3 := congrFun (congrFun hwA (emb i')) (emb i)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h3
  rw [h3]
  by_cases hii : i' = i
  · subst hii; simp
  · rw [if_neg (fun h' => hii (emb.injective h')), if_neg hii, map_zero]

theorem nuW_le_crude (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    nuW Xo c la k a n ≤ max 0 (crudeBd la (DF Dw a) : EReal) := by
  unfold nuW
  refine max_le_max le_rfl ?_
  unfold nuSup
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho =>
    iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  unfold nuLoc
  refine (iInf_le _ C).trans ?_
  letI := io.toAlgebra
  exact (crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).1

omit [StarRing (𝓞 E)] in
theorem card_Lt1_le_finrank_mul : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ τ : E →+* ℂ, Dw.mult τ ≤ ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) := by
        apply Finset.sum_le_sum
        intro τ _
        unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
        split_ifs <;> omega
    _ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul]

end

variable {D : D7}

theorem nuFinAt_of (T : Core D) (hp : T.Q.Pins) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)]
    (hw : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j)
    (hE : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c) (hS : ∀ j, InR D j → ChartSaturated (T.Q.Xo j) T.Q.c) :
    NuFinAt T Dd := by
  intro j hj la
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have hn : Fintype.card (Lt1 (T.Q.Dw j)) ≤ Dd.nW j := by
    refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]; exact (hw j hj).2
  refine ne_top_of_le_ne_top ?_ (nuW_le_crude (hE j hj) (hS j hj) la _ _ _ (fun τ i i' h => (hw j hj).1 τ h) hn)
  rcases le_total (0 : EReal) (crudeBd la (DF (T.Q.Dw j) (Dd.aL j)) : EReal) with h | h
  · rw [max_eq_right h]; exact EReal.coe_ne_top _
  · rw [max_eq_left h]; exact EReal.zero_ne_top

def depRun (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E :=
  depDataOf T EX Tn vd (fun j => wtA (wL j)) (fun j => wtA (wF j)) (fun j => (wL j).n)
    (fun j => ∑ τ, ∑ i, (ka j).aP τ i) fun j => ∑ τ, ∑ i, (ka j).aM τ i

theorem lawsPi_depRun [StarRing (𝓞 D.host.E)] {T : Core D} (h : LawsM T) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j)
    (hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (wL j).n) : LawsPi T (depRun T EX Tn vd wL wF ka) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, ?_, ?_, ?_⟩
  · exact tPos_depDataOf ..
  · exact fun j hj => ⟨(dom_wtA (wL j)).1, hn j hj⟩
  · exact piSplit_depDataOf ..
  · exact piHalf_depDataOf _ _ _ _ _ _ _ _ _ h

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def ProdInLat (ka : WeightFamilies.Wt D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (n : ℕ) : Prop :=
  ∀ s : Fin n → Fin (N + 1), ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧ (F : Tc.R j) = ∏ k, wR (s k)

def SupPTGe (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evC_prod (h : GenFrEx Xo c) (hgt : GenFromTest Xo c h) (Z : Comp Xo c) {n : ℕ} (f : Fin n → Rul Xo c) :
    evC h Z (∏ k, f k) = ∏ k, evC h Z (f k) := by
  let φ : Rul Xo c →* Om Z :=
    { toFun := evC h Z
      map_one' := evalAt_one _ _ _ (hgt Z)
      map_mul' := fun a b => evalAt_mul _ _ a b _ }
  exact map_prod φ f Finset.univ

theorem evC_add (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f + g) = evC h Z f + evC h Z g := evalAt_add _ _ f g _

theorem evC_zero (h : GenFrEx Xo c) (Z : Comp Xo c) : evC h Z (0 : Rul Xo c) = 0 := evalAt_zero _ _ _

theorem evC_smul (h : GenFrEx Xo c) (Z : Comp Xo c) (a : c.F) (f : Rul Xo c) :
    evC h Z (a • f) = algebraMap c.F (Om Z) a * evC h Z f := evalAt_smul _ _ a f _

theorem smul_single_AC (Z : Comp Xo c) (a : 𝓞 c.F) (G : WTZ E) (e : Om Z) :
    a • (AddMonoidAlgebra.single G e : AC Z) = AddMonoidAlgebra.single G (algebraMap c.F (Om Z) (a : c.F) * e) := by
  first
  | rw [AddMonoidAlgebra.smul_single]
  | erw [AddMonoidAlgebra.smul_single]
  rw [Algebra.smul_def]
  congr 1

theorem valC_smul (h : GenFrEx Xo c) (a : 𝓞 c.F) (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h u n ((a : c.F) • f) Z = a • valC h u n f Z := by
  simp only [valC, evC_smul]
  exact (smul_single_AC Z a _ _).symm

end Ev


theorem coe_smul_cusp {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (a : 𝓞 Tc.Q.c.F) (F : (recB hL).Cusp j ka) :
    ((a • F : (recB hL).Cusp j ka) : Tc.R j) = ((a : Tc.Q.c.F) • (F : Tc.R j)) := by
  rfl

def LamConst (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j) (P : ℝ) (n : ℕ) (s : ℝ) : Prop :=
  WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size ≤ P * n * s

theorem htLAM_of [Fintype (Comp (Tc.Q.Xo j) Tc.Q.c)] (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (δ : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Tc.Q.Dw j) → ℤ)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR D.host.E)
    (wR : Fin (N + 1) → Tc.R j) (jc : Comp (Tc.Q.Xo j) Tc.Q.c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Tc.R j) (n0 : ℕ) (th0R : Fin n0 → Tc.R j) (uF0 : WtR D.host.E)
    (nk : ℕ) (thkR : Fin nk → Tc.R j) (MR : Set (Tc.R j)) (etR ta1R ta2R : Tc.R j)
    (nu : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ)
    (ip : (Tc.Q.c.F →+* ℂ) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → ℂ)
    (wsize : WTZ D.host.E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j)
    (hgt : GenFromTest (Tc.Q.Xo j) Tc.Q.c h)
    (hka : wtZ (wtA ka) ka.n = (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 • wtZ uL.1 uL.2)
    (hlam : LAMwAt large₂ (recB hL) j ka C A)
    (hprod : ProdInLat hL j ka wR (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96)
    (hsup : SupPTGe hL j h fn yP ka)
    (hc : LamConst j large₂ C A ka PP0' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM := by
  classical
  intro Z g hg hgZ
  obtain ⟨F, hFM, rfl⟩ : ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧
      g = valC h (wtA ka) ka.n (F : Tc.R j) := by
    clear hgZ
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨F, hFM, hF⟩ := hprod s
      refine ⟨F, hFM, ?_⟩
      funext Z
      rw [hF]
      beta_reduce
      rw [Finset.prod_apply]
      change ∏ k, AddMonoidAlgebra.single (wtZ uL.1 uL.2) (evC h Z (wR (s k))) =
        AddMonoidAlgebra.single (wtZ (wtA ka) ka.n) (evC h Z (∏ k, wR (s k)))
      rw [AddMonoidAlgebra.prod_single, hka, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        evC_prod h hgt Z]
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      funext Z
      simp [valC, evC_zero]
    | add x y _ _ hx hy =>
      obtain ⟨F, hFM, rfl⟩ := hx
      obtain ⟨G, hGM, rfl⟩ := hy
      refine ⟨F + G, Submodule.add_mem _ hFM hGM, ?_⟩
      funext Z
      simp [valC, evC_add, AddMonoidAlgebra.single_add]
    | smul a x _ hx =>
      obtain ⟨F, hFM, rfl⟩ := hx
      refine ⟨a • F, Submodule.smul_mem _ a hFM, ?_⟩
      funext Z
      show a • valC h (wtA ka) ka.n (F : Tc.R j) Z = valC h (wtA ka) ka.n ((a • F : (recB hL).Cusp j ka) : Tc.R j) Z
      rw [coe_smul_cusp hL j ka a F]
      exact (valC_smul h a _ _ _ Z).symm
  have hev : evC h Z (F : Tc.R j) ≠ 0 := fun h0 => hgZ (by simp [valC, h0])
  obtain ⟨F', hF'M, hF'0, hle⟩ := hsup Z F hFM hev
  have hl := hlam F' hF'M hF'0
  refine (neg_le_neg hc).trans (hl.trans ?_)
  unfold WeightFamilies.meanLogSup meanK
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sg _ => ?_) (Nat.cast_nonneg _)
  have hpos : 0 < (recB hL).supN j ka sg F' :=
    lt_of_le_of_ne ((recB hL).supN_nonneg _ _ _ _)
      (fun h0 => hF'0 (((recB hL).supN_eq_zero _ _ _ _).1 h0.symm))
  refine Real.log_le_log hpos ((hle sg).trans (le_of_eq ?_))
  change _ = ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (_ • wtZ uL.1 uL.2) _ P
  rw [hka]

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def LocRingSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    (∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)) ∧
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Top D} (h : LawsP T)

def EtArch (th tableLineDegreeTwo : ℝ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom →
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k)
            (rdU (T.U j σ) η.1 k) x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))

end Formalism.L2.Pj
end
end
