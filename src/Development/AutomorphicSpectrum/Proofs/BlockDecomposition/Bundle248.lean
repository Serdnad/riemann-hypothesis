module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerMemLatticeSubBound
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle198
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle211
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle230
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle231
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle232
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215

@[expose] public section

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.integer_mem_lattice_sub_bound : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], ∀ x : OK l K, ∃ c : ℕ, ∀ M k : ℕ, 2 * c ≤ M → Lat.pk l k (Lat.kP l K x) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub | exact GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub <;> assumption)
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_xi_mem_ideal_and_theta_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧ ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  first | exact @GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | exact GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | (intros; apply GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.flat_base_change_limit_system : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  first | exact @GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo | exact GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo | (intros; apply GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo <;> assumption)
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem d_cup_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {p n m : ℕ} {r : CH.Cn F₁ p} {z : CH.Cn F₂ n} (hr : CH.d F₁ p r = 0) (hz : CH.d F₂ n z = 0) (h : p + n = m) :
    CH.d F₃ m (P.cupC h r z) = 0 := by
  rw [CrystallineSemistableComparison.P.leibniz, hr, hz]
  simp

section Over
variable {K : Type} [Field K] [CharZero K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}
open GlobalTheory.CompanionTheory.RelInjAbs GlobalTheory.CompanionTheory.RelInjZ


theorem kill_over [IsSeparated q] [IsClosedImmersion i] (hTop : TopRes) (hFU : FormUniq) (hOR : OmRes) (hSL : SiteLaws) (hCD : CovDesc) (hZR : ZarRel)
    (hAO : AffOm) (hAR : AffRel) (hFL : FormLaws) (hDW : DWedge) (hDL : DLog) (hFC : FormCup) (hC1 : FirstChernCoboundary) (hCK : ConeKill)
    (D : E.LineData Y) (hQ : Cosieve (On q i))
    (bf : ∀ {V : Scheme.{0}} (a : V ⟶ D.Y), Γ(V, ⊤))
    (bf_nat : ∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), bf (g ≫ a) = g.appTop.hom (bf a))
    (bf_u : ∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), bf a = (D.u a b h : Γ(V, ⊤)) * bf b)
    {m : ℕ} (U : Fin m → Y.Opens) (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (hσ : ∀ α, σ α ≫ D.f = (U α).ι)
    (hU : (⨆ α, U α) = ⊤) (haff : ∀ α α', IsAffineOpen (U α ⊓ U α'))
    (hcov : ∀ α (V : Y.Opens) (h : V ≤ U α), IsAffineOpen V →
      (∃ n, Nonempty (Coord q V n)) ∧ (∃ n, Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) n)) ∧
      RingHom.ker (i.app V).hom = Ideal.span {V.topIso.hom.hom (bf (Y.homOfLE h ≫ σ α))} ∧
      ∀ (a : ℕ) (ω : Om K (Sec q V) a), (show Sec q V from V.topIso.hom.hom (bf (Y.homOfLE h ≫ σ α))) • ω = 0 → ω = 0)
    (r : CH.Cn (G q 1) 2) (hr : CH.d (G q 1) 2 r = 0) (hc1 : IsDlogFirstChernClass q D (clsH (a := 1) q r hr))
    (a n : ℕ) (z : CH.Cn (G q a) n) (hz : CH.d (G q a) n z = 0) (hzr : z ∈ relS (G q a) (On q i) n) :
    RelNull (G q (a + 1)) (On q i) (n + 2)
      (cupC q (a := 1) (a' := a) (Nat.add_comm 1 a) (Nat.add_comm 2 n) r z) := by
  classical
  obtain ⟨hc, -, htop, -, -, -⟩ := hSL K W Y Y q i (𝟙 Y)
  obtain ⟨ε, β, hβ, hβu⟩ := hC1 K Y q D (Fin m) U σ hσ r hr hc1
  let Uc : Fin m → ObjectProperty (Thick (smFun Y q)) := fun α => inU q (U α)
  let Vs : Finset (Fin m) → Y.Opens := fun S => S.inf U
  have hVle : ∀ {α : Fin m} {S : Finset (Fin m)}, α ∈ S → Vs S ≤ U α := fun h => Finset.inf_le h
  have hVT : ∀ {S T : Finset (Fin m)}, S ⊆ T → Vs T ≤ Vs S := fun h => Finset.inf_mono h
  have hVaff : ∀ S : Finset (Fin m), S.Nonempty → IsAffineOpen (Vs S) := fun S hS =>
    affine_finset_inf q U S hS fun o _ => by simpa using haff o o
  have hP : ∀ S : Finset (Fin m), S.Nonempty → capU Uc S = inU q (Vs S) := fun S hS =>
    capU_nonempty _ _ S hS fun T => inU_finset_inf hSL i U S T
  have hk : ∀ {S T : Finset (Fin m)}, S ⊆ T → inU q (Vs T) ≤ inU q (Vs S) := fun h T' hT =>
    (inU_finset_inf hSL i U _ T').2 fun o ho => (inU_finset_inf hSL i U _ T').1 hT o (h ho)
  have hd₁ : ∀ S : Finset (Fin m), S.Nonempty → ∃ d, Nonempty (Coord q (Vs S) d) := fun S ⟨α, hα⟩ =>
    (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).1
  have hd₂ : ∀ S : Finset (Fin m), S.Nonempty → ∃ d, Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ Vs S) d) := fun S ⟨α, hα⟩ =>
    (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.1
  choose dd hdd using hd₁
  choose dd' hdd' using hd₂
  have hE : ∀ (S : Finset (Fin m)) (hS : S.Nonempty) (b : ℕ),
      ∃ e : Om K (Sec q (Vs S)) b →ₗ[K] HV q (Vs S) b b, IsOm q (Vs S) b e ∧ Function.Bijective e := fun S hS b =>
    (hAO K Y q (Vs S) (dd S hS) (hdd S hS) b).2
  choose E hEom hEb using hE
  have hOm := fun (S T : Finset (Fin m)) (h : S ⊆ T) => hOR K Y q (Vs S) (Vs T) (hVT h) (hk h)
  choose φ hφ1 hφ2 hφ3 using hOm
  let P := (grOk (smFun Y q) (Nat.add_comm 1 a)).pair
  have hUc : ∀ α, Cosieve (Uc α) := fun α => hc _
  have h1 : (covSy (G q a) Uc hQ).One a := fun S hS j hj =>
    one_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) a j hj
  have h2 : (covSy (G q (a + 1)) Uc hQ).One (a + 1) := fun S hS j hj =>
    one_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) j hj
  let e₂ : ∀ S : Finset (Fin m), S.Nonempty → (Om K (Sec q (Vs S)) a →ₗ[K] HU (G q a) (capU Uc S) a) := fun S hS =>
    (castH (G q a) (hP S hS) a).toLinearMap ∘ₗ E S hS a
  let e₃ : ∀ S : Finset (Fin m), S.Nonempty → (Om K (Sec q (Vs S)) (a + 1) →ₗ[K] HU (G q (a + 1)) (capU Uc S) (a + 1)) :=
    fun S hS => (castH (G q (a + 1)) (hP S hS) (a + 1)).toLinearMap ∘ₗ E S hS (a + 1)
  let fS : ∀ (α : Fin m) (S : Finset (Fin m)), α ∈ S → Sec q (Vs S) := fun α S hα =>
    (Vs S).topIso.hom.hom (bf (Y.homOfLE (hVle hα) ≫ σ α))
  have pf : ∀ (α α' : Fin m) (S : Finset (Fin m)) (hα : α ∈ S) (hα' : α' ∈ S),
      (Y.homOfLE (hVle hα) ≫ σ α) ≫ D.f = (Y.homOfLE (hVle hα') ≫ σ α') ≫ D.f := fun α α' S hα hα' => by
    simp [hσ]
  let uS : ∀ (α α' : Fin m) (S : Finset (Fin m)), α ∈ S → α' ∈ S → (Sec q (Vs S))ˣ := fun α α' S hα hα' =>
    Units.map (M := Γ((Vs S : Scheme.{0}), ⊤)) (N := Sec q (Vs S)) ((Vs S).topIso.hom.hom : _ →+* Γ(Y, Vs S)).toMonoidHom
      (D.u (Y.homOfLE (hVle hα) ≫ σ α) (Y.homOfLE (hVle hα') ≫ σ α') (pf α α' S hα hα'))
  have hφf : ∀ (α : Fin m) {S T : Finset (Fin m)} (h : S ⊆ T) (hα : α ∈ S), φ S T h (fS α S hα) = fS α T (h hα) := by
    intro α S T h hα
    rw [hφ1]
    refine (rs_topIso (hVT h) _).trans ?_
    rw [← bf_nat, ← Category.assoc, Scheme.homOfLE_homOfLE]
  let kk : ∀ {S T : Finset (Fin m)}, S ⊆ T → capU Uc T ≤ capU Uc S := fun h _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩
  have huf : ∀ α α' S hα hα', fS α S hα = uS α α' S hα hα' * fS α' S hα' := fun α α' S hα hα' =>
    (congrArg (Vs S).topIso.hom.hom (bf_u _ _ (pf α α' S hα hα'))).trans (map_mul _ _ _)
  have hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU Uc S).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q (Vs S)) a)
      (w : Om K (Sec q (Vs S)) a →ₗ[Sec q (Vs S)] Om K (Sec q (Vs S)) (a + 1)),
      (∀ g₀ (g : Fin a → Sec q (Vs S)), w (form K g₀ g) = form K g₀ (Fin.cons (uS α α' S hα hα' : Sec q (Vs S)) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU Uc S).ι ⋙ G q (a + 1))).cls ((pairU P (capU Uc S)).cupC (Nat.add_comm 1 a)
        ((resU (G q 1) (capU_le Uc S hα)).pullC 1 (β α) - (resU (G q 1) (capU_le Uc S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ ((ε : ℤ) • ((↑(uS α α' S hα hα')⁻¹ : Sec q (Vs S)) • w ω)) := by
    intro α α' S hα hα' y hy ω w hw hcls hz
    have := cup_P hFL hFU hFC (hP S ⟨α, hα⟩) (capU_le Uc S hα) (capU_le Uc S hα') (β α) (β α') (E S ⟨α, hα⟩ a)
      (E S ⟨α, hα⟩ (a + 1)) (hEom S _ a) (hEom S _ (a + 1)) ((ε : ℤ) • (↑(uS α α' S hα hα')⁻¹ : Sec q (Vs S)))
      (uS α α' S hα hα' : Sec q (Vs S))
      (fun k₁ k₂ => hβu α α' (Vs S) (hVle hα) (hVle hα') k₁ k₂ (uS α α' S hα hα') (by
        change (Vs S).topIso.inv.hom ((Vs S).topIso.hom.hom _) = _
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
        rfl)) w hw y hy ω hcls hz
    rw [smul_assoc] at this
    exact this
  let x : ((covSy (G q a) Uc hQ).K ∅).X n :=
    ⟨(CH.Mor.restrict (G q a) (capU Uc ∅).ι).pullC n z, fun s hs => hzr _ hs⟩
  have hx : ((covSy (G q a) Uc hQ).K ∅).d n x = 0 := Subtype.ext (by
    change CH.d _ n ((CH.Mor.restrict (G q a) (capU Uc ∅).ι).pullC n z) = 0
    rw [CH.Mor.d_pullC, hz, map_zero])
  have hB := cov_kill hCK hCD hDW hDL hFL P Uc hUc hQ a h1 h2 r hr β hβ (fun S => Sec q (Vs S)) e₂ e₃
    (fun S hS => (castH (G q a) (hP S hS) a).bijective.comp (hEb S hS a))
    (fun S hS => inj_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) (E S hS (a + 1)) (hEom S hS (a + 1)))
    (fun S => kerI q i (Vs S))
    (fun S hS ω => range_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) a (E S hS a) (hEom S hS a) ω)
    (fun S hS ω => range_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) (E S hS (a + 1)) (hEom S hS (a + 1)) ω)
    fS (fun α S hα => (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.2.1)
    (fun α S hα ω => (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.2.2 (a + 1) ω) (ε : ℤ)
    (fun {S T} h => φ S T h) hφf kk
    (fun {S T} h hS hT ω => pull_P (hP S hS) (hP T hT) (kk h) a (E S hS a) (E T hT a) (omMap (φ S T h) a)
      (fun k' ω => hφ3 S T h a _ _ (hEom S hS a) (hEom T hT a) ω) ω)
    (fun {S T} h hS hT ω => pull_P (hP S hS) (hP T hT) (kk h) (a + 1) (E S hS (a + 1)) (E T hT (a + 1))
      (omMap (φ S T h) (a + 1)) (fun k' ω => hφ3 S T h (a + 1) _ _ (hEom S hS (a + 1)) (hEom T hT (a + 1)) ω) ω)
    uS huf hcup n x hx
  have hZ := bij_res_of_eq (capU_empty Uc) hQ (fun _ _ => htop _) (fun _ _ => htop _) (n + 2)
    (hZR K W Y q i hQ (Fin m) ⊤ U hU (fun _ _ => htop _) (a + 1) (n + 2))
  have hd : CH.d (G q (a + 1)) (n + 2) (P.cupC (Nat.add_comm 2 n) r z) = 0 := d_cup_zero P hr hz _
  exact relNull_top hTop (G q (a + 1)) hQ (inU q ⊤) (capU Uc ∅) htop _ hZ (P.cupC (Nat.add_comm 2 n) r z) hd
    (cup_mem_relS P hQ _ r z hzr) _ rfl hB

end Over

end GlobalTheory.CompanionTheory.RelKill
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.scheme_models_spread : GlobalTheory.SpreadingModels.SchemeModels := by
  first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.central_torus_contracts_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | exact GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Rapid (h : C₀(ℝ, ℂ)) : Prop := ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y

def lTr {n : ℕ} {V : Type} (x : G n) (f : Mat n → V) : Mat n → V := fun y => f (x.val * y)

def secCls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) : Set (Lp E.V 2 μ) :=
  {x | ∃ f, Sob μ f ∧ IsSec E f ∧ cls μ f = x}

def Std {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ) : Prop :=
  LgFacts ∧ Unimod ∧ RCalc ∧ SobG ∧ AlgEst ∧ WaveSpeed ∧ WaveCpt ∧ CalcSteps ∧ SmoothOp ∧ PWdecay ∧
    (∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x) ∧
    (∀ x y : Msob μ E.V, ⟪(Ω x : Lp E.V 2 μ), y⟫_ℂ = ⟪(x : Lp E.V 2 μ), Ω y⟫_ℂ) ∧
    (∀ x : Msob μ E.V, ∃ v : Msob μ E.V, (v : Lp E.V 2 μ) = T x ∧ (v : Lp E.V 2 μ) + (Ω (Ω v) : Lp E.V 2 μ) = x) ∧
    (∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) ∧
    (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) ∧
    ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2

def Row {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (h : C₀(ℝ, ℂ)) (v : E.V) (f : Mat n → E.V) : Prop :=
  Sob μ f ∧ IsSec E f ∧ ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ → Sob μ f' → IsSec E f' →
    cls μ f' = F.Φ h (cls μ φ) → ⟪cls μ f, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def FactorRapid : Prop :=
  ∀ h : C₀(ℝ, ℂ), Rapid h → ∃ h₁ h₂ : C₀(ℝ, ℂ), Rapid h₁ ∧ Rapid h₂ ∧ Rapid (star h₂) ∧ h = h₁ * h₂

def EvAdj : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ κ ∈ closure (secCls μ E), ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ →
      Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ φ) → ⟪κ, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def RowExists : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ f, Row μ E F h v f

def RowMatrix : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), (∀ v : E.V, ∃ f, Row μ E F h v f) →
      ∃ A : Mat n → (E.V →L[ℂ] E.V), ∀ v, Row μ E F h v (fun y => A y v)

def AdjSmooth : Prop :=
  ∀ (W V : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (A : W → (V →L[ℂ] V)) (s : Set W),
    (∀ v, ContDiffOn ℝ ∞ (fun y => A y v) s) → ContDiffOn ℝ ∞ (fun y => ContinuousLinearMap.adjoint (A y)) s

def LtSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → Unimod → RCalc →
    ∀ (x : G n) (f : Mat n → V), Sob μ f → Sob μ (lTr x f) ∧ ∀ g ∈ GLs n, Om (lTr x f) g = Om f (x.val * g)

def LtComm : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (x : G n) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → cls μ f' = F.Φ h (cls μ f) →
      cls μ (lTr x f') = F.Φ h (cls μ (lTr x f))

def RowLeft : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), Rapid h → (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ y ∈ GLs n, ∀ v, A (k.1 * y) v = A y (E.ρ k⁻¹ v)

def ActFormula : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ f ∈ CE E, Cpt f → ∀ f', Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ f) →
        ∀ x ∈ GLs n, act μ E (fun y => ContinuousLinearMap.adjoint (A y)) f x = f' x

def WaveRep : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ f ∈ CE E, Cpt f → ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b

def WaveUniq : Prop :=
  WaveSpeed → CalcSteps → RCalc → ∀ (n : ℕ) (E : KMod n) (u u' : ℝ → Mat n → E.V), IsWave E u → IsWave E u' →
    (∀ x ∈ GLs n, u 0 x = u' 0 x) → ∀ t, ∀ x ∈ GLs n, u t x = u' t x

def PhiRes : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ N : ℕ, 1 ≤ N →
      F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) = F.Φ (toC0 (hg c g)) * T ^ N

def WaveInt : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N → IsWave E U →
      (∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b) →
      ∀ f', Sob μ f' → cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b →
        ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • U t x = f' x

def SupportRow : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ) (h : C₀(ℝ, ℂ)), IsBump g T₀ → Rapid h →
      (∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
        cls μ f' = F.Φ h (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x) →
      ∃ R : ℝ, ∀ (v : E.V) (f : Mat n → E.V), Row μ E F h v f → ∀ y ∈ GLs n, R < lg y → f y = 0

end GlobalTheory.CompanionTheory.KerFc
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

theorem phi_keeps_sections : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      LgFacts → Unimod → RCalc → SobG → CalcSteps →
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ (h : C₀(ℝ, ℂ)) (f : Mat n → E.V), Sob μ f → IsSec E f →
        ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h (cls μ f) := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hSG hCS hΩ h f hf hs
  obtain ⟨-, -, -, -, hC, hO, hCp, -, hP, hCT, -, hFr, hOF, hI, hD⟩ := hCS
  have hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x :=
    (hCT n μ E.V hL hU hR hSG hP hFr hC hO hCp hOF hI hD).1
  obtain ⟨f', hf', hcl, -⟩ := GlobalTheory.CompanionTheory.WaveFc.Asm.pres hC hO hL hU hR hSG hP F hrep hΩ h hf
  exact ⟨f', hf', GlobalTheory.CompanionTheory.WaveFc.Asm.sec_pres E hC hO hL hU hR F hrep hΩ h hf hs hf' hcl, hcl⟩

end GlobalTheory.CompanionTheory.FcSmooth
end

section


theorem _root_.GlobalTheory.T.absolute_fourier_coefficients : PositivityTheory.RgBcC.Fc.AbsFC := by
  first | exact @GlobalTheory.CompanionTheory.FuncCalc.absFC | exact GlobalTheory.CompanionTheory.FuncCalc.absFC | (intros; apply GlobalTheory.CompanionTheory.FuncCalc.absFC <;> assumption)
end

section


theorem _root_.GlobalTheory.T.absolute_cutoff_bound : PositivityTheory.RgBcC.Fc.AbsCut := by
  first | exact @GlobalTheory.CompanionTheory.FcCut.absCut | exact GlobalTheory.CompanionTheory.FcCut.absCut | (intros; apply GlobalTheory.CompanionTheory.FcCut.absCut <;> assumption)
end

section


theorem _root_.GlobalTheory.T.casimir_operator_formula : PositivityTheory.RgBcC.Fc.OmFormula := by
  first | exact @GlobalTheory.CompanionTheory.Casimir.omFormula | exact GlobalTheory.CompanionTheory.Casimir.omFormula | (intros; apply GlobalTheory.CompanionTheory.Casimir.omFormula <;> assumption)
end

section


theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  first | exact @GlobalTheory.CompanionTheory.FcCls.clsFacts | exact GlobalTheory.CompanionTheory.FcCls.clsFacts | (intros; apply GlobalTheory.CompanionTheory.FcCls.clsFacts <;> assumption)
end
