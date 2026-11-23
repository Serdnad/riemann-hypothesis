module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HyperbolicIntegrabilityLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pInf_alg (v : InfinitePlace F) (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have e : TR.pInf F (algebraMap F (Ad F) x) v = (v.embedding x).re := by
    rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
    simp
  rw [e, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

omit [IsTotallyReal F] in
theorem fin_zc (u : (Af F)ˣ) : finGL F 2 (zc F u) = Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F u) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

def rr (γ : GL (Fin 2) F) : GL (Fin 2) (TR.Rinf F) := Matrix.GeneralLinearGroup.map ((TR.pInf F).comp (algebraMap F (Ad F))) γ

theorem gv_rr (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (γ : GL (Fin 2) F) (v : InfinitePlace F) : gv v (rr γ) = (mkDat c χ).r v γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg v (γ i j))

theorem rat_eq (γ : GL (Fin 2) F) : ratGL F 2 γ = TR.infGL F 2 (rr γ) * finGL F 2 (jF F γ) := by
  rw [← TR.infGL_mul_finGL (ratGL F 2 γ)]
  rfl

omit [IsTotallyReal F] in
theorem sc_comm (s : Ideles F) (a : GA F 2) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * a = a * Matrix.GeneralLinearGroup.scalar (Fin 2) s :=
  Units.ext (Matrix.scalar_commute (s : Ad F) (fun _ => Commute.all _ _) a.val).eq

theorem aut (hb : B1b) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (φ : TR.Sm F 2) (hφ : TR.IsAutForm φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (γ : GL (Fin 2) F) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    f ((mkDat c χ).act γ (fun v => gv v g • iP), jF F γ * x) =
      (mkDat c χ).J k γ (fun v => gv v g • iP) * f ((fun v => gv v g • iP), x) := by
  have e1 : (mkDat c χ).act γ (fun v => gv v g • iP) = fun v => gv v (rr γ * g) • iP := funext fun v => by
    change (mkDat c χ).r v γ • gv v g • iP = _
    rw [map_mul, mul_smul, gv_rr c χ]
  have e4 : TR.infGL F 2 (rr γ * g) * finGL F 2 (jF F γ * x) = ratGL F 2 γ * (TR.infGL F 2 g * finGL F 2 x) := by
    rw [rat_eq, map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (TR.infGL F 2 g), TR.infGL_comm, mul_assoc]
  have e5 : ∀ v, j1 (k v) (gv v (rr γ * g)) iP = j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP) * j1 (k v) (gv v g) iP :=
    fun v => by rw [map_mul, hb.1, gv_rr c χ]
  rw [e1, ← hf, ← hf, e4, hφ.left, Finset.prod_congr rfl fun v _ => e5 v, Finset.prod_mul_distrib]
  change _ = (∏ v, j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP)) * _
  ring

theorem lev (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (χ : Hc c →* ℂˣ) (hχ : IsChi c ω χ) (φ : TR.Sm F 2)
    (hcent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (hfix : ∀ u ∈ Kc c, TR.finRep F 2 u φ = φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : Hc c) :
    f ((fun v => gv v g • iP), x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f ((fun v => gv v g • iP), x) := by
  obtain ⟨⟨κ, hκ, z0, hz⟩, hv⟩ := hχ h
  have e5 : φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) = φ.1 (TR.infGL F 2 g * finGL F 2 x) :=
    congrArg (fun ψ : TR.Sm F 2 => ψ.1 (TR.infGL F 2 g * finGL F 2 x)) (hfix κ hκ)
  have e6 : TR.infGL F 2 g * finGL F 2 (x * (h : GF F)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F z0) * (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) := by
    rw [hz, map_mul, map_mul, fin_zc, sc_comm]
    simp only [mul_assoc]
  rw [← hf, ← hf, hv κ hκ z0 hz, e6, hcent, e5, mul_assoc]

theorem bdd (hb : B1b) (k : InfinitePlace F → ℕ) (φ : TR.Sm F 2) (C : ℝ) (hC : ∀ g, ‖φ.1 g‖ ≤ C)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    ‖f ((fun v => gv v g • iP), x)‖ * nrm k (fun v => gv v g • iP) ≤ C := by
  have e : ∀ v, ‖j1 (k v) (gv v g) iP‖ * |(gv v g • iP).1.im| ^ ((k v : ℝ) / 2) = 1 := fun v => by
    rw [hb.2.2.2.2.1]
    simp [iP]
  rw [← hf g x, norm_mul, nrm, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
  simp only [e, Finset.prod_const_one, mul_one]
  exact hC _

end UpperTheory.Esk.HyperbolicIntegrabilityLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.hyperbolic_terms_integrable_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H0 → UpperTheory.Esk.H1a → UpperTheory.Esk.H1b → UpperTheory.Esk.H1c → UpperTheory.Esk.H1 := by
  intro hb hc h0 h1a h1b h1c F _ _ _ k c ω χ hω hχ φ hφ hcusp
  obtain ⟨f, hf⟩ := h1a F k c ω φ hω hφ
  refine ⟨f, ⟨h1b F k c ω φ hω hφ f hf, fun γ z x => ?_, fun z x h => ?_, ?_⟩, hf⟩
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.aut hb k c χ φ hφ.aut f hf γ g x
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    by_cases h0φ : φ = 0
    · have e : ∀ g x, f (fun v => gv v g • iP, x) = 0 := fun g x => by rw [← hf g x, h0φ]; simp
      change f (_, x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f (_, x)
      rw [e, e, mul_zero]
    obtain ⟨-, hfix, -⟩ := h0 F k c ω φ hφ h0φ
    exact HyperbolicIntegrabilityLemmas.lev k c ω χ hχ φ hφ.cent hfix f hf g x h
  · obtain ⟨C, hC⟩ := h1c F k c ω φ hω hφ hcusp
    refine ⟨C, fun z x => ?_⟩
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.bdd hb k φ C hC f hf g x
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem stab_open (ρ : Representation ℂ G V) (x : V) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (hx : ∀ g ∈ U, ρ g x = x) : IsOpen {g | ρ g x = x} := by
  rw [isOpen_iff_mem_nhds]
  intro g₀ hg₀
  have ho : IsOpen ((fun g => g₀⁻¹ * g) ⁻¹' U) := hU.preimage (by fun_prop)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using h1)) fun g hg => ?_
  have h2 : ρ (g₀⁻¹ * g) x = x := hx _ hg
  have hg₀' : ρ g₀ x = x := hg₀
  change ρ g x = x
  calc ρ g x = ρ g₀ (ρ (g₀⁻¹ * g) x) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = x := by rw [h2, hg₀']

def smV (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {x | IsOpen {g | ρ g x = x}}
  add_mem' := fun {x y} hx hy => stab_open ρ _ _ (IsOpen.inter hx hy) ⟨by simp, by simp⟩
    fun g hg => by
      have h1 : ρ g x = x := hg.1
      have h2 : ρ g y = y := hg.2
      rw [map_add (f := _), h1, h2]
  zero_mem' := by
    change IsOpen {g | ρ g 0 = 0}
    simp only [map_zero, Set.setOf_true]
    exact isOpen_univ
  smul_mem' := fun a x hx => stab_open ρ _ _ hx (by simp) fun g hg => by
    have h1 : ρ g x = x := hg
    rw [map_smul, h1]

theorem smV_stable (ρ : Representation ℂ G V) (g : G) : smV ρ ≤ Submodule.comap (ρ g) (smV ρ) := by
  intro x hx
  change IsOpen {h | ρ h (ρ g x) = ρ g x}
  refine stab_open ρ _ ((fun h => g⁻¹ * h * g) ⁻¹' {h | ρ h x = x}) ((show IsOpen {h | ρ h x = x} from hx).preimage (by fun_prop))
    (by simp) fun h hh => ?_
  have e : ρ (g⁻¹ * h * g) x = x := hh
  calc ρ h (ρ g x) = ρ g (ρ (g⁻¹ * h * g) x) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]
    _ = ρ g x := by rw [e]

theorem smV_smooth (ρ : Representation ℂ G V) : GlobalTheory.PRep.IsSmooth (ρ.subrepresentation (smV ρ) (smV_stable ρ)) := by
  intro x
  have e : {g | ρ.subrepresentation (smV ρ) (smV_stable ρ) g x = x} = {g | ρ g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [e]
  exact x.2

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem fix_of (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2) (hφ : IsHolV k c ω φ) :
    φ ∈ Hi.fixd (TR.finRep F 2) (Kc c) := by
  let ρ := (TR.finRep F 2).subrepresentation (smV (TR.finRep F 2)) (smV_stable _)
  have hx : φ ∈ smV (TR.finRep F 2) := hφ.aut.level
  have h := fixGlob F _ ρ (smV_smooth _) c ⟨φ, hx⟩ fun w u hu => Subtype.ext (hφ.level w u hu)
  intro u hu
  exact congrArg Subtype.val (h u hu)

private def rot (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith

omit [NumberField F] [IsTotallyReal F] in
private theorem rot_add (θ θ' : TR.Rinf F) : rot (θ + θ') = rot θ * rot θ' := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem sign_holV {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) (v : InfinitePlace F) :
    ((ω.locInf v (-1) : ℂˣ) : ℂ) = Complex.exp (Complex.I * (k v : ℕ) * Real.pi) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Subtype.ext (funext h))
  set e : TR.Rinf F := Pi.single v 1 with he
  have hr0 : rot ((0 : ℝ) • e) = 1 := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [rot]
  have hd0 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * TR.infGL F 2 (rot (t • e)))) (Complex.I * (k v : ℕ) * φ.1 g) 0 := fun g => by
    have h1 := TR.hasDerivAt_curve φ g (fun t : ℝ => rot (t • e))
      (TR.toL (Matrix.single 0 1 e) - TR.toL (Matrix.single 1 0 e)) hr0 (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
        have hc := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).cos
        have hs := ((hasDerivAt_id (0 : ℝ)).mul_const (e u)).sin
        fin_cases i <;> fin_cases j
        · simpa [rot] using hc
        · simpa [rot] using hs
        · simpa [rot] using hs.fun_neg
        · simpa [rot] using hc)
    rw [← TR.lie_apply, map_sub] at h1
    exact h1.congr_deriv (congrArg (fun x : TR.Sm F 2 => x.1 g) (hφ.wt v))
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rot (t • e))) with hf
  have hd : ∀ t, HasDerivAt f (Complex.I * (k v : ℕ) * f t) t := fun t => by
    have h1 := HasDerivAt.comp_sub_const t t ((sub_self t).symm ▸ hd0 (g * TR.infGL F 2 (rot (t • e))))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [mul_assoc, ← map_mul, ← rot_add, ← add_smul, add_sub_cancel]
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t * Complex.exp (-(Complex.I * (k v : ℕ) * t))) 0 t := fun t => by
    have h1 := (hd t).mul (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k v : ℕ))).fun_neg.cexp)
    exact h1.congr_deriv (by simp; ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hc t).differentiableAt) (fun t => (hc t).deriv) Real.pi 0
  have hu : (1 - 2 * e) * (1 - 2 * e) = 1 := by
    funext w
    by_cases h : w = v
    · subst h; simp [he]; norm_num
    · simp [he, h]
  let u : (TR.Rinf F)ˣ := ⟨1 - 2 * e, 1 - 2 * e, hu, hu⟩
  have h3 : rot (Real.pi • e) = GeneralLinearGroup.scalar (Fin 2) u := by
    ext i j w
    by_cases h : w = v
    · subst h
      fin_cases i <;> fin_cases j <;> simp [rot, u, he] <;> norm_num
    · fin_cases i <;> fin_cases j <;> simp [rot, u, he, h]
  have h4 : Units.map (GlobalTheory.CuspRep.corner (TR.sInf F)) u = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
    refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
    · change (1 - TR.infEq F 1 + TR.infEq F (1 - 2 * e)) w = Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
      rw [map_one, sub_self, zero_add]
      change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((1 - 2 * e) w) = _
      by_cases h : w = v
      · subst h
        rw [show (1 - 2 * e) w = -1 by simp [he]; norm_num]
        simp
      · simp [he, h]
    · change (1 : Af F) - 0 + 0 = 1
      simp
  simp only [hf, hr0, h3, TR.infGL, map_one, mul_one] at h2
  rw [GlobalTheory.CuspRep.cornerGL_scalar, h4, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent] at h2
  rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, Complex.exp_neg, mul_right_comm,
    mul_eq_right₀ hg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at h2
  exact h2

theorem sgn_of {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) : Sgn k ω := by
  intro v
  rw [sign_holV hφ h0 v, show Complex.I * ((k v : ℕ) : ℂ) * (Real.pi : ℂ) = (k v : ℕ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem fin_zc (z : (Af F)ˣ) : finGL F 2 (zc F z) = GeneralLinearGroup.scalar (Fin 2) (finId F z) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

theorem chi_of {k c} {ω : HChar F} {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (h0 : φ ≠ 0) : ∃ χ, IsChi c ω χ := by
  have hfix := fix_of k c ω φ hφ
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Subtype.ext (funext h))
  have h1 : ∀ z, zc F z ∈ Kc c → (ω.1.comp (finId F)) z = 1 := by
    intro z hz
    have e := congrArg (fun ψ : TR.Sm F 2 => ψ.1 g) (hfix _ hz)
    change φ.1 (g * finGL F 2 (zc F z)) = φ.1 g at e
    rw [fin_zc, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, mul_eq_right₀ hg] at e
    exact Units.ext e
  obtain ⟨χ, hχ⟩ := exChi (GF F) (Af F)ˣ (Kc c) (zc F) (ω.1.comp (finId F)) (fun z => zc_center z) h1
  exact ⟨χ, hχ⟩

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
theorem UpperTheory.Esk.hyperbolic_terms_setup_proof : UpperTheory.Esk.H0 := by
  intro F _ _ _ k c ω φ hφ h0
  exact ⟨sgn_of hφ h0, fix_of k c ω φ hφ, chi_of hφ h0⟩
end
end
