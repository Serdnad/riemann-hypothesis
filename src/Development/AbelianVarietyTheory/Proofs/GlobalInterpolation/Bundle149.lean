module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle110
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle158
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle160
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle153
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCoordinatesValueLatticesEqWeylLattices
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle147
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle108
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle102
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_primitiveRoots_coeffField_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  first | exact @GlobalTheory.trueCols_exists_primitiveRoots | exact GlobalTheory.trueCols_exists_primitiveRoots | (intros; apply GlobalTheory.trueCols_exists_primitiveRoots <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  exact @GlobalTheory.PerQ.trueWeights_built
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.classPairing_integral_form_row_isIntegral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  first | exact @GlobalTheory.PairAtClass.pair_integral | exact GlobalTheory.PairAtClass.pair_integral | (intros; apply GlobalTheory.PairAtClass.pair_integral <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne GlobalTheory.MomN
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomN.PeriodData

variable {q : ℕ} [Fact q.Prime]

theorem laws_and_chart (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (L : PeriodPair)
    (hd : d.Prime) (h7 : d % 16 = 7) (hs : Split d q) (hL : IsOK d L)
    (hD : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) (hδ : δ ^ 12 = discr d) (hδ0 : δ ≠ 0) (hθ : IsTh d θ) :
    ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ ∧
      ∃ M : Mdl q, M.ι = ι ∧ IsOK d M.L ∧ M.MChart (Ω / ι δ) := by
  obtain ⟨M, rfl, rfl, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h7 hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h7 hs hL hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hn⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h7 hs hL hω₀
  set ω := ω₀ * zc a
  have hι : M.ι δ ≠ 0 := by simpa using hδ0
  refine ⟨ω * M.ι δ, ?_, ?_, M, rfl, hL, ?_⟩
  · rw [norm_mul, (GenusOne.norm_root_eq M hok δ (hδ.trans hD.symm)).1, GenusOne.norm_period M ω hω]
  · rw [mul_div_cancel_right₀ _ hι]
    have hN := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M ω θ hd h7 hs hL hω hθ
    refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M ω θ hd h7 hs hL hω hθ hn, hN⟩
    have hU := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1
    have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left _, 0, 0, by simp⟩
    have := hN 1 1 (fun _ => 1) (fun _ => 0) t 1 (fun _ => h0) ht
      (by simpa [hU] using GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h7 hs hL hω hθ)
    simpa [hU] using this
  · rw [mul_div_cancel_right₀ _ hι]; exact hω

end GlobalTheory.MomN.PeriodData

namespace GlobalTheory.MomN

theorem exists_per : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q →
    ∃ (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per d ι δ₀ θ Ω := by
  intro d q _ ι hd h7 hs
  obtain ⟨δ₀, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr d) (by norm_num : 0 < 12)
  obtain ⟨⟨L, hL, hD⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h7
  have hδ0 : δ₀ ≠ 0 := (GenusOne.thetaLaws_unit_period d q δ₀ hd h7 hs hδ).choose_spec.2.1
  obtain ⟨Ω, hΩ, hT, hM⟩ := PeriodData.laws_and_chart d ι δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  refine ⟨δ₀, θ, Ω, hθ, hδ, hδ0, fun ι' => ?_, hΩ, hT, hM⟩
  obtain ⟨Ω', h1, h2, -⟩ := PeriodData.laws_and_chart d ι' δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  exact ⟨Ω', h1, h2⟩

end GlobalTheory.MomN
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.cmTheta_baseVector_translates_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  first | exact @GlobalTheory.MomN.translates_latInt | exact GlobalTheory.MomN.translates_latInt | (intros; apply GlobalTheory.MomN.translates_latInt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem exists_levCh_of_levelPrime : LevelPrime → ∀ (eps cs : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → 0 < cs → Std C → ∃ x0 : ℝ, ∀ (cD ch : ℝ) (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, 0 < du u) → 0 < Ds → (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ Lv : LevCh P, Lv.duStar = du ∧ Lv.Dstar = Ds ∧ Lv.GamP = GamS C s P.R := by
  intro hLP eps cs C he he' hcs hC
  obtain ⟨x1, h1⟩ := hLP eps cs he he' hcs
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨max (max x1 x2) (max x3 (max 2 ((1 / cs) ^ 4))), ?_⟩
  intro cD ch s P q1 a b c du Ds hs hx hOK hdu hDs hwin
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4, hx5⟩ := hx
  obtain ⟨-, -, hb, -⟩ := h2 s hs hx2
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, -, hm, -⟩ := h3 s P.R hs hx3 hOK.rank
  have hx0 : 0 < s.x := by linarith
  have hxone : 1 ≤ s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hm2 : (2 : ℝ) ≤ P.R.m := by exact_mod_cast P.R.two_le_m
  have hmf : (P.R.m : ℝ) ≤ P.R.f := by exact_mod_cast P.R.m_le_f
  have hGam : 1 < GamS C s P.R := by
    unfold GamS
    rw [Real.one_lt_exp_iff]
    have : (0 : ℝ) < P.R.f := by linarith
    have : (0 : ℝ) < P.R.m := by linarith
    have : 0 < C.CGam := by linarith
    have : 0 < s.L := by linarith
    positivity

  have hk : (P.R.k : ℝ) ≤ s.x ^ 5 := by
    have : (P.R.k : ℝ) ≤ P.R.r := by exact_mod_cast hkr
    have e : s.x ^ (5 : ℝ) = s.x ^ 5 := by exact_mod_cast Real.rpow_natCast s.x 5
    exact this.trans (hr.trans_eq e)
  have hb41 : s.x ^ 41 ≤ s.b := by
    have e : s.x ^ (41 : ℝ) = s.x ^ 41 := by exact_mod_cast Real.rpow_natCast s.x 41
    rw [e, Real.rpow_one] at hb
    exact (le_mul_of_one_le_right (by positivity) hX1).trans hb
  have hk8 : 2 * (P.R.k : ℝ) ^ 8 ≤ s.b := by
    have h8 : (P.R.k : ℝ) ^ 8 ≤ (s.x ^ 5) ^ 8 := pow_le_pow_left₀ (by positivity) hk 8
    calc 2 * (P.R.k : ℝ) ^ 8 ≤ s.x * (s.x ^ 5) ^ 8 := mul_le_mul hx4 h8 (by positivity) hx0.le
      _ = s.x ^ 41 := by ring
      _ ≤ s.b := hb41
  have hg : ∀ i, (P.H.g i : ℝ) ≤ s.b ^ 9 := fun i => by
    calc (P.H.g i : ℝ) ≤ 2 * ((P.R.k : ℝ) * s.b) ^ 8 := (hOK.val.2.2.2.2.1 i).2
      _ = (2 * (P.R.k : ℝ) ^ 8) * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := mul_le_mul_of_nonneg_right hk8 (by positivity)
      _ = s.b ^ 9 := by ring

  have hcm : 1 ≤ cs * P.R.m := by
    have a1 : 1 / cs ≤ s.x ^ ((1 : ℝ) / 4) := by
      have a0 : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hx5 (by norm_num)
      have e : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) = 1 / cs := by
        have := Real.pow_rpow_inv_natCast (x := 1 / cs) (n := 4) (by positivity) (by norm_num)
        simpa using this
      rwa [e] at a0
    have a2 : s.x ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    have a3 : 1 / cs ≤ P.R.m := a1.trans (a2.trans hm)
    rw [div_le_iff₀ hcs] at a3
    linarith
  have hXL : s.X' ≤ Real.exp (cs * P.R.m * s.L) := by
    unfold Scale.X'
    refine Real.exp_le_exp.2 ?_
    have a1 : s.x ^ (s.eps / 3) ≤ s.L :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    exact a1.trans (le_mul_of_one_le_left (by linarith) hcm)
  have hp : (P.H.pde : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.1 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).1
    · exact h
  have hp' : (P.H.pde' : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.2 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).2
    · exact h
  refine GlobalTheory.Mem.LevelChoice.exists_levCh P du Ds _ hdu hDs hGam fun u => ?_
  have hT0 : 0 < (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
    have : (0 : ℝ) < du u := by exact_mod_cast hdu u
    have : 0 < GamS C s P.R := by linarith
    positivity
  obtain ⟨T, hT, hlo, hhi, hN⟩ := h1 s P.R P.H.condN P.H.d (P.H.g 0) (P.H.g 1) _ hs hx1 hOK.rank hOK.val.modRow
    (P.H.g_prime 0).one_le (P.H.g_prime 1).one_le (hg 0) (hg 1) hT0 (hwin u)
  have hXT : s.X' ≤ T :=
    hXL.trans (((Real.le_log_iff_exp_le hT0).1 (hwin u)).trans hlo)
  have hM : 1 ≤ P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 := by
    have hn : 0 < P.H.QS := P.H.QS_pos
    have hq : 0 < P.H.q := P.H.hyp.1.pos
    have hd : 0 < P.H.d := P.H.hyp.2.1.pos
    have h0 := (P.H.g_prime 0).pos
    have h1 := (P.H.g_prime 1).pos
    exact Nat.succ_le_of_lt (by positivity)
  obtain ⟨⟨π, hK, hπ, hc⟩, -⟩ := GlobalTheory.EX.normOne_host P.R P.H _ T hM hN
  refine ⟨π, T, hT, ?_, ?_, hK, hπ, hc, hlo, hhi⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

end GlobalTheory.EX.OB
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelic_fourierSeries_of_summable_coefficients : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ (P : (Fin N → AF F) → ℂ) (c : (Fin N → F) → ℂ), Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ) → Summable (fun ξ => ‖c ξ‖) → ∀ u, P u = ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) := by
  first | exact @GlobalTheory.SWQ.FourierSeries.fourier_series | exact GlobalTheory.SWQ.FourierSeries.fourier_series | (intros; apply GlobalTheory.SWQ.FourierSeries.fourier_series <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (M : PtModel B.ch i) (R : B.Real i sp M), i ≤ D.R.m → B.Sees → ∃ Co : M.Coord, Co.Ok ∧ R.ValIs Co := by
  first | exact @GlobalTheory.LvT.Built.ValLat.exists_coord | exact GlobalTheory.LvT.Built.ValLat.exists_coord | (intros; apply GlobalTheory.LvT.Built.ValLat.exists_coord <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evaluationMap_trueChain_forms_to_forms :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I →
      ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (l0 : TC.Law0 I l)
        (u : B.Word) (a : I.ι),
        (∀ φ ∈ ((TC.tw I l l0 Z).fm u a).Fi B.R.m,
          GlobalTheory.PerQ.PtT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u a φ ∈
            ((TC.tw I l l0 Z).fm u a).ptC) ∧
        ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).SgInterlace := by
  intro B X I _ l Z l0 u a
  have hs : ∀ τ, (TC.perIn I u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hW := GlobalTheory.LvT.BuiltChain.weights_ok (TC.perIn I u a) (B.hcW u) B.fields.emb hs
  refine ⟨?_, ?_⟩
  · intro φ hφ
    let M := TC.fm I l u a
    have latticeImage : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x hx
      obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := TC.perIn I u a)
        B.fields.emb B.embLL (B.hcW u) GlobalTheory.LvT.BuiltChain.branching_ok
        (l.ch u a) (l.per u a) (fun τ => (hW τ).1) (fun τ => (hW τ).2)
        ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
      exact ⟨y, hy⟩
    have rationalImage : ∀ x, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x
      have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
        rw [(M.lat_good B.R.m).2.2]
        trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact latticeImage x hx
      | zero => exact ⟨0, by simp⟩
      | add x x' _ _ hx hx' =>
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', by rw [map_add, map_add, map_add, map_add, hy, hy']⟩
      | smul r x _ hx =>
        obtain ⟨y, hy⟩ := hx
        refine ⟨r • y, ?_⟩
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hy, LinearMap.map_smul, LinearMap.map_smul]
    have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
      intro y

      rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    have hφ' : φ ∈ M.Fi B.R.m := hφ
    rw [← (M.emb_basis B.R.m).2] at hφ'
    have hle : Submodule.span ℂ (Set.range fun c => M.emb B.R.m ((M.lat B.R.m).b c)) ≤
        M.ptC.comap ((TC.per I l u a).lowerMap ∘ₗ (TC.per I l u a).evz) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨y, hy⟩ := rationalImage ((M.lat B.R.m).b c)
      show (TC.per I l u a).lowerMap ((TC.per I l u a).evz _) ∈ M.ptC
      rw [← hy]
      exact ptMem y
    exact hle hφ'
  · intro τ i
    obtain ⟨ha, hb⟩ := (hW τ).1 i
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT,
      GlobalTheory.Mem.Col2.shW] at ha hb
    constructor
    · show (B.wts.sgW τ).w i ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩
      change 0 ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ).w i + _) at hb
      linarith
    · show (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ).w i
      change 0 ≤ (B.wts.sgW τ).w i + _ - ((Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
      linarith
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PerQ

theorem lowerTieTwAt_to_lib : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup),
    GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  rintro D T u μ ⟨a, b, P, hP⟩
  exact ⟨a, b, ⟨P.br, P.coM, P.coP, P.Pt_eq, P.lat_co, P.pt_co⟩, hP⟩

end GlobalTheory.PerQ
end

section

noncomputable section

namespace GlobalTheory.EX.OB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField



theorem exists_sizeData_over : ∀ (eps cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P) (D : D7), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R → Over D P Lv → RecOK s C cD D → HostArith D.host ∧ (∃ L : SizeData₂ D, L.sc = s ∧ WtEq L a b ∧ Val C cD ch L) ∧ D.R = P.R ∧ D.host.TT.image Formalism.HC.Frame.A.val = P.H.TT.image Formalism.HC.Frame.A.val ∧ D.host.T2 = P.H.T2 ∧ D.host.q = P.H.q ∧ D.host.d = P.H.d ∧ D.host.g = P.H.g ∧ D.host.pde = P.H.pde ∧ D.host.pde' = P.H.pde' ∧ P.H.levelPrimes ⊆ D.host.levelPrimes ∧ D.host.u0.val = P.H.u0.val ∧ (∀ l, (G.hP D l).val = (hPH P.H l).val) ∧ ∃ eW : D.what₂.Word ≃ P.Word, ∀ u l, wordBits D u l = if h : l < P.R.k - 2 then c (eW u) ⟨l, h⟩ else false := by
  intro eps cD ch C h0 h1 hC hcD hch
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv D hs hx hP hG hO hR
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hB, rfl⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (Pre.ofCh P Lv sp hT hY hA hV hz).level_split
  refine ⟨⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Finset.subset_union_left, rfl, fun l => rfl, Equiv.refl _, ?_⟩
  · obtain ⟨L, e1, e2, e3, e4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog hR.del hP.ct2
      hP.card hR.etaF (fun u => by
        have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
        rw [e, hG, GamS, Real.log_exp]; rfl)
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) hR.untw
    refine ⟨L, e1, ?_, e4⟩
    intro t t' htt
    have : t.1 = t' := Formalism.HC.Frame.A.val_injective _ htt
    rw [e2, e3]
    subst this
    exact ⟨rfl, rfl⟩
  · intro u l
    unfold wordBits
    by_cases h : l < P.R.k - 2
    · have h' : l < D.R.k - 2 := h
      rw [dite_eq_left h', dite_eq_left h]
      have τ : Tau P.R := tauPl D (false, 0)
      have a1 := D.s.u_letter u τ l h'
      have a2 := hP.code u τ l h
      have a3 := a1.symm.trans a2
      have hpos := D.s.Del_pos
      rw [← hR.del] at a3
      show D.s.letter u ⟨l, h'⟩ = c u ⟨l, h⟩
      have a4 : (if D.s.letter u ⟨l, h'⟩ = true then D.s.Del else 0) = (if c u ⟨l, h⟩ = true then D.s.Del else 0) :=
        sub_right_injective a3
      revert a4
      cases D.s.letter u ⟨l, h'⟩ <;> cases c u ⟨l, h⟩ <;> simp [hpos.ne', hpos.ne]
    · have h' : ¬ l < D.R.k - 2 := h
      rw [dite_eq_right h', dite_eq_right h]

end GlobalTheory.EX.OB

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem usage₉ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl), Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) (GlobalTheory.PerQ.Co.bP I u a w c) ∧ (∀ x, iniH (N_m_succ B.R) (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) = ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧ (∀ x, (I.perIn u a).tz * (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) = x (Br.iL (N_m_succ B.R))) ∧ Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) (GlobalTheory.PerQ.Co.bM I u a w c) := by
  intro B X I _hI l u a w c
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  have hlat := (l.per u a).step.lsh_lat c.1 ((I.perIn u a).S'.rep c)
  have hP : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _)
      (GlobalTheory.PerQ.Co.bP I u a w c) := by
    let d := ((I.stX a).rep c).1.1.deco
    have hN := GlobalTheory.LvT.Pts.span_eq_top_of_unimodular d.1.N d.2.lat d.2.uni
    have hspan : Submodule.span B.fields.E
        ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) = ⊤ :=
      top_unique (hN.ge.trans (Submodule.span_mono d.2.N_le_Lsh))
    obtain ⟨g, hg⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis
      (B.places.resChar w) B.fields.E _ hlat.fg hspan
    exact Classical.epsilon_spec (p := fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g) ⟨g, hg⟩
  refine ⟨hP, ?_⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_localBasis_snoc_of_localBasis (N_m_succ B.R) (I.perIn u a).tz (l.per u a).tz_ne
    (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c))
    ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))
    (fun x => (l.per u a).Lsh_til c.1 ((I.perIn u a).S'.rep c) x) (B.places.resChar w) (GlobalTheory.PerQ.Co.bP I u a w c)
    (B.places.resChar_prime w) hP
  exact Classical.epsilon_spec (p := fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g) ⟨g, hg⟩

end GlobalTheory.PerQ.Co
end
