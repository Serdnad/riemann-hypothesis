module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle171
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtNZ

theorem exists_sec_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ t : SAB H (Sp R), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∃ σ : SecAt t.G t.PP.L (𝟙 (Sp R)), NZ t.G t.PP.L (𝟙 (Sp R)) σ := by
  intro E _ _ _ H R _ _ _ hB t ⟨P⟩
  haveI := t.comm
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IsNoetherianRing R := hB.1.1
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R P.D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : P.D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good P.D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) P.D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract P.D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit P.D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫
        padd P.D.toPre.P.A (snd _ _) (toUnit _ ≫ P.D.toPre.c 0) = padd P.D.toPre.P.A (𝟙 _) (toUnit _ ≫ P.D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ P.D.toPre.c 0 = toUnit _ ≫ P.D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ η[P.D.toPre.P.A] = toUnit _ ≫ η[P.D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : P.D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl P.U f₀ ⟨_, hx, hxn⟩
  have key : ∃ σ : H0 P.U.LG.L 1, ∃ g, t.G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    ⟨σ, GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl P.U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem⟩
  rw [P.bundle] at key
  obtain ⟨σ, g, hg, hn⟩ := key
  refine ⟨GlobalTheory.TorRef.upSec t.G σ, GlobalTheory.Ex.OnModel.toBase t.G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase t.G ≫ (fst (Over.mk (𝟙 (Sp R))) t.G).left = t.G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ExtNZ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThUniq

theorem comp_pow' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_perm_pts {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N : ℕ} {pt q : Fin N → (Over.mk x ⟶ G)}
    {c d : Fin N → K} (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' q d) :
    ∃ σ : Equiv.Perm (Fin N), ∀ b, q b = pt (σ b) := by
  have key : ∀ b, ∃ a, q b = pt a := by
    intro b
    let i := algebraMap K (AlgebraicClosure K)
    let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
    have hp : (u ≫ q b) ^ (m ^ 2) = 1 := by
      rw [← comp_pow', (h'.2.1 b).1, MonObj.comp_one]
    obtain ⟨a, ha⟩ := h.2.2 (AlgebraicClosure K) i (u ≫ q b) hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
    exact (cancel_epi (spMap i)).1 (by rw [← ha, Over.comp_left]; rfl)
  choose f hf using key
  have hinj : Function.Injective f := fun b b' e => h'.1 ((hf b).trans ((congrArg pt e).trans (hf b').symm))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

end GlobalTheory.UMin.ThUniq

namespace GlobalTheory.UMin.ThUniq

theorem theta_lists_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S), Odd m → (m : K) ≠ 0 → Odd m' → (m' : K) ≠ 0 → PolFib G L g x → (∀ (θ : SecAt G L x) (pt pt' : Fin N → (Over.mk x ⟶ G)) (c d : Fin N → K), ThList G L ρ m x θ pt c → ThList G L ρ m x θ pt' d → ∃ σ : Equiv.Perm (Fin N), ∀ b, d b = c (σ b)) ∧ ∀ (c d : Fin N → K) (c' d' : Fin N' → K), HasTh₂ G L ρ m m' x c c' → HasTh₂ G L ρ m m' x d d' → ∃ (a : K) (σ : Equiv.Perm (Fin N)) (σ' : Equiv.Perm (Fin N')), a ≠ 0 ∧ (∀ b, d b = a * c (σ b)) ∧ ∀ b, d' b = a * c' (σ' b) := by
  intro S G _ _ L ρ hL hρ g m m' N N' K _ x hm hmK hm' hmK' hpol
  have tv : ∀ (k : ℕ), Odd k → (k : K) ≠ 0 → ∀ (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K),
      SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ →
      ThG G L ρ k θ p (GlobalTheory.ZH.fn c) → ThG G L ρ k θ' p (GlobalTheory.ZH.fn c') → c' = a * c :=
    fun k hk hkK θ θ' p a c c' hs hc hc' =>
      (GlobalTheory.T.thetaConstant_unique_and_linear_in_section S G L ρ hL hρ g k K x θ θ' p a c c' hk hkK hpol hs hc).1 hc'
  have gen : ∀ θ θ' : SecAt G L x, IsGenSec G L _ θ →
      ∃ a : K, SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ := by
    intro θ θ' h
    obtain ⟨r, hr⟩ := h θ'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r, ?_⟩
    have e : @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)) = r := by
      show ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom r = r
      rw [Iso.hom_inv_id]; rfl
    rw [e]
    exact Subtype.ext (funext hr)
  refine ⟨fun θ pt pt' c d h h' => ?_, fun c d c' d' H H' => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_pts h h'
    refine ⟨σ, fun b => ?_⟩
    have e1 : SecM.ofSec G θ = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G θ := by
      rw [show @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) = 1 from map_one _, one_smul]
    rw [tv m hm hmK θ θ (pt (σ b)) 1 (c (σ b)) (d b) e1 (h.2.1 (σ b)) (by rw [← hσ b]; exact h'.2.1 b), _root_.one_mul]
  · obtain ⟨θ, pt, pt', hg, h1, h1'⟩ := H
    obtain ⟨θ₂, q, q', hg₂, h2, h2'⟩ := H'
    obtain ⟨σ, hσ⟩ := exists_perm_pts h1 h2
    obtain ⟨σ', hσ'⟩ := exists_perm_pts h1' h2'
    obtain ⟨a₀, ha₀⟩ := gen θ θ₂ hg
    obtain ⟨a₁, ha₁⟩ := gen θ₂ θ hg₂
    have E : ∀ b, d b = a₀ * c (σ b) := fun b =>
      tv m hm hmK θ θ₂ _ a₀ _ _ ha₀ (h1.2.1 (σ b)) (by rw [← hσ b]; exact h2.2.1 b)
    have E' : ∀ b, d' b = a₀ * c' (σ' b) := fun b =>
      tv m' hm' hmK' θ θ₂ _ a₀ _ _ ha₀ (h1'.2.1 (σ' b)) (by rw [← hσ' b]; exact h2'.2.1 b)
    by_cases h0 : a₀ = 0
    · have F : ∀ b, c (σ b) = a₁ * d b := fun b =>
        tv m hm hmK θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ b]; exact h2.2.1 b) (h1.2.1 (σ b))
      have F' : ∀ b, c' (σ' b) = a₁ * d' b := fun b =>
        tv m' hm' hmK' θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ' b]; exact h2'.2.1 b) (h1'.2.1 (σ' b))
      refine ⟨1, σ, σ', one_ne_zero, fun b => ?_, fun b => ?_⟩
      · have e := E b
        rw [h0, MulZeroClass.zero_mul] at e
        rw [F b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
      · have e := E' b
        rw [h0, MulZeroClass.zero_mul] at e
        rw [F' b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
    · exact ⟨a₀, σ, σ', h0, E, E'⟩

end GlobalTheory.UMin.ThUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.RealTh

theorem exists_pow_eq (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    {k : ℕ} (hk : (k : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ k = 1) : ∃ y : Over.mk x ⟶ P.A, y ^ k = z := by
  have := P.isAb.comm
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have hk2 : ((k ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hk
  have c₁ := TorsionFieldExt.card_torsion hL P x hk
  have c₂ := TorsionFieldExt.card_torsion hL P x hk2
  let H₁ := (powMonoidHom k : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  let H₂ := (powMonoidHom (k ^ 2) : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  have e₁ : Nat.card H₁ = k ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₁, MonoidHom.mem_ker])).trans c₁
  have e₂ : Nat.card H₂ = (k ^ 2) ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₂, MonoidHom.mem_ker])).trans c₂
  have : Finite H₂ := Nat.finite_of_card_ne_zero (by rw [e₂]; positivity)
  have : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [e₁]; positivity)
  let ψ : H₂ →* (Over.mk x ⟶ P.A) := (powMonoidHom k).comp H₂.subtype
  have hker : Nat.card ψ.ker = k ^ (2 * P.g) := by
    rw [← e₁]
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1.1, ?_⟩) ⟨fun a b h => ?_, fun a => ?_⟩)
    · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)
    · apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : H₁ => (q : Over.mk x ⟶ P.A)) h
    · refine ⟨⟨⟨a.1, ?_⟩, ?_⟩, rfl⟩
      · have := a.2
        simp only [H₁, MonoidHom.mem_ker, powMonoidHom_apply] at this
        simp [H₂, MonoidHom.mem_ker, sq, pow_mul, this]
      · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 a.2)
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker, e₂, ← pow_mul, mul_comm 2, pow_mul,
    sq, mul_comm] at hmul
  have hrange : Nat.card ψ.range = Nat.card H₁ := by
    rw [e₁]
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) hmul).symm
  have hle : ψ.range ≤ H₁ := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H₂, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [ψ, H₁, MonoidHom.mem_ker, ← pow_mul, ← sq, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle hrange.ge
  have hzm : z ∈ ψ.range := heq ▸ (show z ∈ H₁ by simpa [H₁, MonoidHom.mem_ker] using hz)
  obtain ⟨y, hy⟩ := hzm
  exact ⟨y.1, hy⟩

end GlobalTheory.UMin.RealTh


open GlobalTheory.UMin.RealTh in
theorem GlobalTheory.UMin.thList_real : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i N pt c H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hkK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := S.unit.map (i.comp (algebraMap o S.R))
    rw [map_natCast] at this
    exact this.ne_zero
  let β : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  let u : Over.mk (spMap j ≫ spMap i ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp S.R)) := Over.homMk (spMap j) rfl
  have hkK' : ((S.r * S.N : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast j]; exact (map_ne_zero j).2 hkK
  have down : ∀ y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A, y ^ (S.r * S.N) = 1 → ∃ b, y = β ≫ ρ.pt b := by
    intro y hy
    obtain ⟨b, hb, -⟩ := ρ.pt_bij (AlgebraicClosure K) (spMap j ≫ spMap i ≫ 𝟙 _) (u ≫ y)
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
    refine ⟨b, TorsionFieldExt.comp_injective u _ ?_⟩
    refine hb.symm.trans (Over.OverMorphism.ext ?_)
    simp [u, β]
  constructor
  · intro x
    have h := H.2.1 x
    obtain ⟨b, hb⟩ := down (pt x ^ (S.r * S.N)) (by rw [← pow_mul, ← sq]; exact h.1)
    exact ⟨b, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt x) (c x) hb h⟩
  · intro b
    have tb : ρ.pt b ^ (S.r * S.N) = 1 := (ρ.fr_tors b).1
    obtain ⟨y, hy⟩ := exists_pow_eq hL ρ.P (spMap j ≫ spMap i ≫ 𝟙 _) hkK' (u ≫ β ≫ ρ.pt b)
      (by rw [← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    obtain ⟨a, ha⟩ := H.2.2 (AlgebraicClosure K) j y
      (by rw [sq, pow_mul, hy, ← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    have e1 : u ≫ pt a = y := Over.OverMorphism.ext ha.symm
    have e2 : pt a ^ (S.r * S.N) = β ≫ ρ.pt b :=
      TorsionFieldExt.comp_injective u _ (by
        show u ≫ _ = u ≫ _
        rw [MonObj.comp_pow, e1, hy])
    exact ⟨a, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt a) (c a) e2 (H.2.1 a)⟩
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

theorem _root_.GlobalTheory.T.normal_finite_dominant_refinement : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Mean4O.Cover Y),
    ∃ (G : Scheme.{0}) (_ : IsIntegral G) (_ : GlobalTheory.IsNormalScheme G) (g : G ⟶ V₁.G) (k : G ⟶ V₂.G),
      IsFinite g ∧ IsDominant g ∧ k ≫ V₂.π = g ≫ V₁.π := by
  first | exact @GlobalTheory.Mean4O.CommonGen.exists_common | exact GlobalTheory.Mean4O.CommonGen.exists_common | (intros; apply GlobalTheory.Mean4O.CommonGen.exists_common <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.GradedForm

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}

def lineGram (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (x : Root m) (y z : CxPts X.str σ) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((grD (gramAt E H x.1 y z) x.2 : ℝ) : ℂ)

variable [Finite ι] {E : Fr (ratOf X) m m} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem grD_pos (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) : 0 < grD (gramAt E H x.1 y y) x.2 :=
  ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (h.posDef y _ (E.nonempty (under y)).choose_spec x.1)).2.1 x.2).1

theorem lineGram_smooth (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) :
    SmoothUnitAt (atlas X σ) (lineGram E H x y) y := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 (grD_pos h x y).ne')
  · filter_upwards [(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H h y _ (E.nonempty (under y)).choose_spec x.1).2 c hc] with v hv
    intro a b
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp v ((GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).2 x.2)

theorem isGramPair_lineGram (h : IsMetricFr E H) (x : Root m) :
    IsGramPair (atlas X σ) (lineGram E H x) (lineGram E H x) := by
  refine ⟨fun y => ⟨lineGram_smooth h x y, lineGram_smooth h x y⟩, fun y => ?_⟩
  have hy := (E.nonempty (under y)).choose_spec
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ hy] with z hyz
  have hz := (E.nonempty (under z)).choose_spec
  set A := (E.nonempty (under y)).choose with hA
  set B := (E.nonempty (under z)).choose with hB
  have hP := (Fr.mem_iff hyz).1 hz
  have hhol := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X _ ((B * A⁻¹) x.1) z (fun i j => mem_O_ratOf.1 ((hP x.1).1 i j)) (hP x.1).2.1
    (mem_O_ratOf.1 (hP x.1).2.2.1)
  have hval : ∀ w : CxPts X.str σ, A ∈ E.S (under w) → B ∈ E.S (under w) →
      Par m ⊤ ((B * A⁻¹).map (ratVal · w)) := fun w h1 h2 => by
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom w
    exact ((Fr.mem_iff h1).1 h2).map_of _ ψ hψ
  let T : CxPts X.str σ → Matrix (Fin 1) (Fin 1) ℂ := fun w _ _ => ratVal ((B * A⁻¹) x.1 x.2 x.2) w
  have hT : HolUnitAt (atlas X σ) T z := by
    refine ⟨?_, fun c hc _ _ => hhol.2 c hc x.2 x.2⟩
    rw [Matrix.det_fin_one]
    have hp := hval z hyz hz x.1
    have hd := hp.2.1
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hp.2.2.2 i j i.2 hij)] at hd
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hd x.2 (Finset.mem_univ _))
  refine ⟨T, T, T, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hyz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hz] with w h1 h2
  rw [and_self]
  have hp := hval w h1 h2 x.1
  have e := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (h.posDef w A h1 x.1) (fun i j hij => hp.2.2.2 i j i.2 hij)
    (isUnit_iff_ne_zero.2 hp.2.1)).2 x.2
  rw [← h.trans w A h1 B h2 x.1] at e
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply]
  change ((grD (H B w x.1) x.2 : ℝ) : ℂ) = ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2) * ((grD (H A w x.1) x.2 : ℝ) : ℂ) *
    star ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2)
  rw [e, mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem chernFld_lineGram (h : IsMetricFr E H) (x : Root m) :
    chernFld (atlas X σ) (lineGram E H x) 1 = grF E H x := by
  funext p
  have hs := ((lineGram_smooth h x p.pt).2 p.1.1 p.2).self_of_nhds
  have e := GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms _ 1 (fun v => lineGram E H x p.pt (p.ch.symm v))
    (fun _ v => grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2) p.crd hs
    (fun _ => by
      have : p.ch.symm p.crd = p.pt := p.ch.left_inv p.2
      rw [this]; exact grD_pos h x _)
    (Eventually.of_forall fun v => ⟨fun i j hij => absurd (Subsingleton.elim i j) hij.ne, fun _ => rfl⟩) 1
  refine e.trans ?_
  rw [esymm_one, Fin.sum_univ_one, aeval_X]
  rfl

theorem dbarCoh_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  intro F _ σ X ι _ m E H h x
  rw [← chernFld_lineGram h x]
  exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (isGramPair_lineGram h x) 1

end GlobalTheory.ChernCalc.GradedForm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem torMatch_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (g₂ : V →+* V₂) (β₂ : G₂.left ⟶ G'.left), Function.Injective g₂ → (∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V)) → ∀ ρ ρ₂, TorMatch U U' g β ρ → TorMatch U' U₂ g₂ β₂ ρ₂ → TorMatch U U₂ (g₂.comp g) (β₂ ≫ β) (ρ₂.comp ρ) := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ hVb G' _ _ hG' D' A' U' g β V₂ _ _ _ hV₂b G₂ _ _ hG₂ D₂ A₂ U₂ g₂ β₂
    hg₂ hkV ρ ρ₂ h₁ h₂
  intro F _ _ _ _ hF k hk τ τ₂ q q₂ a a₂ hτ₂ hττ hqy hqt hq₂y hq₂t ha ha₂
  have hinj : Function.Injective ((algebraMap (FractionRing V₂) F).comp ((algebraMap V₂ (FractionRing V₂)).comp g₂)) :=
    (algebraMap (FractionRing V₂) F).injective.comp ((IsFractionRing.injective V₂ (FractionRing V₂)).comp hg₂)
  letI : Algebra (FractionRing V) F := (IsFractionRing.lift hinj).toAlgebra
  have hV : ∀ v, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) v) =
      algebraMap (FractionRing V₂) F (algebraMap V₂ (FractionRing V₂) (g₂ v)) := fun v =>
    IsFractionRing.lift_algebraMap hinj v
  have hk' : IsUnit (k : V) := hkV k hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  let τ' : Multiplicative D'.toPre.X →* Fˣ := τ₂.comp (AddMonoidHom.toMultiplicative ρ₂)
  have hτ' : τ' ^ k = 1 := MonoidHom.ext fun χ => DFunLike.congr_fun hτ₂ _
  obtain ⟨q', hq'y, hq't⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (k := k) τ' hτ'
  obtain ⟨hV', _⟩ := hVb
  obtain ⟨f', ⟨i', -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV' D' A' G' hG' U' F k hk1
  have e₁ := h₁ F (fun r => by rw [hF, hV]; rfl) k hk τ τ' q q' a (f' q') hτ' hττ hqy hqt hq'y hq't ha ((i' _ _).2 rfl)
  have e₂ := h₂ F hV k hk' τ' τ₂ q' q₂ (f' q') a₂ hτ₂ (fun _ => rfl) hq'y hq't hq₂y hq₂t ((i' _ _).2 rfl) ha₂
  rw [e₁, reassoc_of% e₂]

end GlobalTheory.Poinc.Eq8
end
