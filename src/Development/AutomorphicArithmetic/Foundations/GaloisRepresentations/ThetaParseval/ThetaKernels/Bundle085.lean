module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle080
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.ExpNeOfLt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle077
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle063
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeylConjugateExponentialParabolic
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem deg_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0)
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    (x : d.G) : fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  set s := s0 d.m d.n with hsdef
  set A : d.G → ℂ := fun g => iteratedDeriv j (Ê · g) s with hAdef
  have hAc : Continuous A := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) s * 2)) • d.I Φ + A := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hfcB : ∀ x', fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x' =
      fc d.B.ψ d.b nb lam 𝓖 A T x' - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x') := by
    intro x'
    rw [hB, (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d hc T x').1 _ _ _ hIc hAc hIi hAi]; ring
  let w : InfinitePlace F := Classical.arbitrary _
  obtain ⟨y, hy⟩ := dilEx d.n (Pi.single L.i₀ 1) 1
  obtain ⟨pp, qq, e, hpq, hhol⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holA_k H R hmn hΦ hv hE w j hj hlow
  obtain ⟨hlawA, huA⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holCoef_k H R L w hc hT A hAc hAi pp qq e hpq hhol
  obtain ⟨uM, ν, 𝓤, hu⟩ := (H.uEx F E σ d R L).1
  obtain ⟨nb', lam', 𝓖', hc'⟩ := H.coefEx F E σ L.sd
  obtain ⟨t', hct⟩ := H.cTSplit F E σ d R L _ _ hsec hEis
  have hspl : ∀ z : ℂ, t' < z.re → ∃ c₂ : d.G → ℂ,
      (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x = _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c₂ x) ∧
      ∀ x, c₂ (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c₂ x := by
    intro z hz
    obtain ⟨c₂, h1, h2⟩ := hct z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hu T T' hT
    exact ⟨c₂, h1, fun x => h2 w 1 y x hy⟩
  let c2 : ℂ → d.G → ℂ := fun z => if h : t' < z.re then Classical.choose (hspl z h) else 0
  have hc2 : ∀ z : ℂ, t' < z.re → (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x =
      _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c2 z x) ∧
      ∀ x, c2 z (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c2 z x := by
    intro z hz
    simp only [c2, dif_pos hz]
    exact Classical.choose_spec (hspl z hz)
  have havg_smul : ∀ (c : ℂ) (φ : d.G → ℂ) x', _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => c * φ g) T x' =
      c * _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x' := by
    intro c φ x'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc, mul_assoc]
    simp only [integral_const_mul]
  have hhol1 := _root_.PositivityTheory.SiegelWeilFormula.AStep.avgHol_k H L hE hc T hT hu
  have hsep := lawSep U p (max t t') s j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x)
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T (R.ι w y * x))
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x) (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x))
    (fun z => c2 z x) (fun z => c2 z (R.ι w y * x)) (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)
    (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x)) (d.n : ℂ) (-2) hUo hR hs hp hj (hhol1 x).1 (hhol1 _).1
    (fun i hi => by
      rw [(hhol1 x).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun i hi => by
      rw [(hhol1 _).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 x])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 _])
    (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    (fun z hz => by
      rw [(hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).2 x]
      congr 1; push_cast; ring_nf)
  have havgA : ∀ x', iteratedDeriv j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x') s = fc d.B.ψ d.b nb lam 𝓖 A T x' := by
    intro x'
    rw [(hhol1 x').2 j]
    show _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 A T x' = _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, huA uM ν 𝓤 hu, setIntegral_const]
    simp [Measure.real, hu.2.2.2]
  rw [havgA, havgA] at hsep
  have hth : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x) = Complex.exp (d.m : ℂ) * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x := by
    have := valLaw (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x)
      (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x)) 0 (d.n : ℂ) 2 s _ _
      (fun z _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneLaw_k H R L hΦ w hc' T' 1 y hy z x]; congr 1; push_cast; ring_nf)
      (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    have e2 : (d.n : ℂ) + 2 * s = d.m := by rw [hsdef, s0]; ring
    rw [e2] at this
    linear_combination this / 2
  have hA1 := hlawA 1 y hy x
  rw [Complex.ofReal_one, one_mul] at hA1
  rw [hfcB x]
  rw [hA1, hth] at hsep
  have e3 : (d.n : ℂ) + -2 * s = ((2 * d.n - d.m : ℕ) : ℂ) := by
    have h2 : ((2 * d.n - d.m : ℕ) : ℂ) = 2 * (d.n : ℂ) - d.m := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h2, hsdef, s0]; ring
  rw [e3] at hsep
  have hne := exp_ne_of_lt hmn
  have key : (Complex.exp ((2 * d.n - d.m : ℕ) : ℂ) - Complex.exp (d.m : ℂ)) *
      (fc d.B.ψ d.b nb lam 𝓖 A T x - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)) = 0 := by
    linear_combination -hsep
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Fintype.card d.κ = Fintype.card (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := by
  rw [card_eq d.bs d.dd.e, Fintype.card_prod, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.core (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (e : ((d.κ → AF F) → ℂ) →ₗ[ℂ] d.Fn) (C : ℂ), C ≠ 0 ∧
    Set.BijOn e (schA F d.κ : Set _) (schA F d.κ : Set _) ∧
    (∀ l ∈ (adeleClass F).adm d.κ, l ∘ₗ e ∈ (adeleClass F).adm d.κ) ∧
    ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := by
  classical
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hF : IsTotallyReal F := d.ok.good.cm.1
  have hD := d.ok.dbl
  let τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d := Fintype.equivOfCardEq (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ) (fun w w' => by rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hbs : bᵀ * J * b = J := by
    calc bᵀ * J * b = bᵀ * (aᵀ * J * a) * b := by rw [ha]
      _ = (a * b)ᵀ * J * (a * b) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [hab, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hF hψ b hbs
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hsurj : ∀ u, ∃ w, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = u := fun u => ⟨d.dd.e.symm (act (b.map (algebraMap F (AF F))) u), by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']⟩
  have hheis : ∀ w, ∀ Ψ ∈ schA F d.κ, e (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) Ψ) = d.dd.rho d.B.ψ w (e Ψ) := fun w Ψ hΨ => by
    rw [h.Heisenberg₂ _ Ψ hΨ, hinv]
    rfl
  have hadm := isOp_adm h d.l hD.adm
  obtain ⟨C, hC⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ d.κ (d.l ∘ₗ e) hadm (fun y φ hφ => by
    obtain ⟨w, hw⟩ := hsurj (0, y)
    obtain ⟨Z, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, hheis _ φ hφ]
    exact hD.kill Z _ (h.maps φ hφ))
  have hT : ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := fun Ψ hΨ X => by
    have h1 := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ)) Ψ hΨ)
    rw [LinearMap.comp_apply, hheis _ Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame] at h1
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, h1]
    simp [schr]
  refine ⟨τ, e, C, fun hC0 => ?_, h.bijOn hψ, fun l hl => isOp_adm h l hl, hT⟩
  obtain ⟨Φ, hΦ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ
  obtain ⟨Ψ, hΨ, rfl⟩ := (h.bijOn hψ).surjOn hΦ
  have h0 : ∀ y : Matrix (Fin d.m) (Fin d.n) E,
      d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) (e Ψ)) = 0 := fun y => by
    rw [← hheis _ Ψ hΨ]
    have := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (incM F (Matrix.fromCols y (-y)))) Ψ hΨ)
    rw [LinearMap.comp_apply] at this
    rw [this, hC0, zero_mul]
  have h2 := hD.theta (e Ψ) hΦ
  simp only [h0] at h2
  exact hθ (h2.unique hasSum_zero)
end Adp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij : _root_.PositivityTheory.SiegelWeilFormula.TBij_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨τ, e, C, hC, hbij, -, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.core d
  have hcomp : ∀ Ψ ∈ schA F d.κ, (fun c => d.T (e Ψ) (d.cmb c)) = C • fun x : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F => Ψ (x ∘ τ) :=
    fun Ψ hΨ => by
      funext c
      rw [hT Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]
      rfl
  refine ⟨fun Φ hΦ => ?_, fun f hf => ?_, fun Φ hΦ h0 => ?_⟩
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    show (fun c => d.T (e Ψ) (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)
    rw [hcomp Ψ hΨ]
    exact Submodule.smul_mem _ C (comp_schA τ hΨ)
  · have hg : (fun c => f (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := hf
    have hΨ : C⁻¹ • (fun x : d.κ → AF F => f (d.cmb (x ∘ τ.symm))) ∈ schA F d.κ :=
      Submodule.smul_mem _ _ (comp_schA τ.symm hg)
    refine ⟨e _, hbij.mapsTo hΨ, funext fun X => ?_⟩
    rw [hT _ hΨ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]
    congr 1
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d X]
    congr 1
    funext i
    simp
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    have hz : Ψ = 0 := by
      funext v
      have := congrFun h0 (d.cmb (v ∘ τ.symm))
      rw [hT Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb] at this
      simpa [hC] using this
    rw [hz, map_zero]
end PositivityTheory.SiegelWeilFormula.TBij
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem stab_dec_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {x : d.G} (hx : x ∈ rat2 σ d.Y) (hf : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x) :
    ∃ (s : d.G) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) (γ' : G2 σ L.Y), s ∈ rat2 σ d.Y ∧ w₁ * s * w₁⁻¹ ∈ par2 σ d.Y ∧ γ' ∈ rat2 σ L.Y ∧
      inFrame L.b γ' = (inFrame d.b x).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) ∧ x = s * (cM c.1 * L.j γ') := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) x hx
  have hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    apply kfour.inclR_injective (F := F)
    have h1 := hf r
    rw [hG0] at h1
    simp only [incM, Matrix.map_apply] at h1
    rw [h1]
    by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]
  have hform := form_E hε x hG0
  have hy := yrow_zero hform hx0
  set H := G0.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) with hH_def
  have hH := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.blockH_form_k L hform hx0 hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨g', hg'⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hg'r : g' ∈ rat2 σ L.Y := kunf.rat_of_inFrame hg'
  have hg'i : inFrame L.b g'⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hg']
    exact Matrix.inv_eq_right_inv hIA
  set n := x * L.j g'⁻¹ with hn_def
  have hnF : inFrame d.b n = incM F (G0 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
    rw [hn_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hG0, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hg'i, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k, kfour.incM_mul']
  have hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_E_k L hx0 hy hHH'
  have hnr : n ∈ rat2 σ d.Y := mul_mem hx (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hg'r))
  set N0 := G0 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H' with hN0
  set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀
  set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀
  set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀
  have hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0 := form_E hε n hnF
  have hpz : σ z₀ = -(((ε : ℤ) : E) * z₀) := M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0
  have hpd := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.delta_par_k h hε
  have hε0 : (((ε : ℤ) : E)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1
  have hfix : σ (z₀ / δ) = z₀ / δ := by
    rw [map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]
  obtain ⟨a₀, ha₀⟩ := fixed_in_F d.ok.good.cm (z₀ / δ) hfix
  let c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L := ⟨(GlobalTheory.ThK.incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀, rfl⟩⟩
  set s := n * (cM c.1)⁻¹ with hs_def
  have hsr : s ∈ rat2 σ d.Y := mul_mem hnr (inv_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h c.2.1 c.2.2))
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom e = e := map_intCast _ _
  have hN : inFrame d.b n = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀) * inFrame d.b (cM c.1) := by
    apply M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse
    · exact kunf.frame_eq hε n
    · have hUS := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.U_sExp_k (ε := ε) (L := L) hσ (GlobalTheory.ThK.incV F b₀)
      have hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1)) := kunf.frame_eq hε (cM c.1)
      unfold M.U at hUS hUC ⊢
      rw [Matrix.transpose_mul, Matrix.map_mul]
      calc (inFrame d.b (cM c.1))ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            ((_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom * (inFrame d.b (cM c.1)).map (cA σ).toRingHom)
          = (inFrame d.b (cM c.1))ᵀ * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom) * (inFrame d.b (cM c.1)).map (cA σ).toRingHom := by
            simp only [Matrix.mul_assoc]
        _ = kunf.jw d.n e := by rw [hUS, hUC]
    · rw [hnF]; exact NQ.map _ hnq0
    · exact NQ.mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.nq_sExp_k _ _) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.nq_cM_k h _)
    · obtain ⟨r1, r2, r3, r4⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.row_sC_k h e (GlobalTheory.ThK.incV F b₀) (GlobalTheory.ThK.incV F u₀) (algebraMap F (AF F) a₀)
      intro c'
      rw [hnF]
      rcases c' with k | k
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r4]
          have := hnq0.1 (Sum.inl L.i₀)
          simp only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
          simp [incM, this]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r1]; rfl
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r3]
          have e1 : algebraMap F (AF F) a₀ • inclR (F := F) (AF F) δ = inclR (F := F) (AF F) z₀ := by
            have : z₀ = algebraMap F E a₀ * δ := by rw [ha₀, div_mul_cancel₀ _ h.δ0]
            rw [this, map_mul]
            show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F] δ
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.algebraMap_eq_smul_one]
          rw [e1, hz₀]
          have hcA : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => rfl

          simp [incM, GlobalTheory.ThK.incV, hcA, map_add (f := _), map_sum, map_mul]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r2]; rfl
  have hS : inFrame d.b s = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀) := by
    have h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1 := by
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    rw [hs_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine ⟨s, c, g', hsr, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.weyl_conjugate_exponential_parabolic h hS, hg'r, ?_, ?_⟩
  · rw [hg', hG0]; rfl
  · rw [hs_def, hn_def, map_inv]; group
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end
