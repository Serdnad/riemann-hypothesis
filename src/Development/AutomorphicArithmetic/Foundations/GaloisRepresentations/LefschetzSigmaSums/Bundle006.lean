module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.Gen.BaseChange

theorem UpperTheory.Gal.LocalSmoothExtension.modelBc_of :
    MapEq → ModelBc := by
  intro hM G R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N M
  obtain ⟨o', ⟨mo⟩⟩ := exists_gObjMap_pull (pullback.fst M.s (spMap τ)) M.univ
  let U : GObj gb₂ N (pullback.snd M.s (spMap τ)) := up hρ ht pullback.condition.symm o'
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R₂) (o : GObj gb₂ N s'),
      ∃! j : S ⟶ pullback M.s (spMap τ), j ≫ pullback.snd M.s (spMap τ) = s' ∧ Nonempty (GObjMap o U j) := by
    intro S s' o
    let u : GObj gb₁ N (s' ≫ spMap τ) := down hρ ht rfl o
    obtain ⟨a, ⟨ha, ⟨ma⟩⟩, hun⟩ := M.rep S _ u
    let j : S ⟶ pullback M.s (spMap τ) := pullback.lift a s' ha
    have j₁ : j ≫ pullback.fst M.s (spMap τ) = a := pullback.lift_fst _ _ _
    have j₂ : j ≫ pullback.snd M.s (spMap τ) = s' := pullback.lift_snd _ _ _
    obtain ⟨mj, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j (pullback.fst M.s (spMap τ)) mo).2 (j₁.symm ▸ ma)
    have mj' : GObjMap o U j := ⟨mj.φ, mj.φ₂, mj.cart, mj.sq, mj.act, mj.pol, mj.eta⟩
    refine ⟨j, ⟨j₂, ⟨mj'⟩⟩, ?_⟩
    rintro j' ⟨h₂, ⟨m'⟩⟩
    have m'' : GObjMap u o' j' := ⟨m'.φ, m'.φ₂, m'.cart, m'.sq, m'.act, m'.pol, m'.eta⟩
    obtain ⟨n, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j' (pullback.fst M.s (spMap τ)) mo).1 m''
    have e : j' ≫ pullback.fst M.s (spMap τ) = a :=
      hun _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂], ⟨n⟩⟩
    apply pullback.hom_ext
    · rw [e, j₁]
    · rw [h₂, j₂]
  refine ⟨⟨pullback M.s (spMap τ), pullback.snd M.s (spMap τ), U, hrep⟩, pullback.fst M.s (spMap τ),
    IsPullback.of_hasPullback M.s (spMap τ), ⟨⟨mo.φ, mo.φ₂, mo.cart, mo.sq, mo.act, mo.pol, mo.eta⟩⟩⟩
end

section

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem UpperTheory.Gal.LocalSmoothExtension.homEx_of :
    HomEx := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  have ext'' : ∀ {T : Over S₁} (u v : T ⟶ o₁''.A), u.left ≫ m''.φ = v.left ≫ m''.φ → u = v := by
    intro T u v h
    apply Over.OverMorphism.ext
    exact m''.cart.1.hom_ext h (by rw [Over.w u, Over.w v])
  have p' : ∀ (T : Over S₁) (x : T ⟶ o₁'.A), (pushHom m'.cart T x).left = x.left ≫ m'.φ :=
    fun _ _ => rfl
  have p'' : ∀ (T : Over S₁) (x : T ⟶ o₁''.A), (pushHom m''.cart T x).left = x.left ≫ m''.φ :=
    fun _ _ => rfl
  refine ⟨?_, fun ψ₁ ψ₂ h => ext'' ψ₁ ψ₂ h, ?_⟩
  · intro ψ hψ
    haveI := hψ
    have w : (m'.φ ≫ ψ.left) ≫ o''.A.hom = o₁'.A.hom ≫ f := by
      rw [Category.assoc, Over.w ψ, m'.cart.1.w]
    let ψ₁ : o₁'.A ⟶ o₁''.A :=
      Over.homMk (m''.cart.1.lift (m'.φ ≫ ψ.left) o₁'.A.hom w) (m''.cart.1.lift_snd _ _ w)
    have hψ₁ : ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left := m''.cart.1.lift_fst _ _ w
    refine ⟨ψ₁, ?_, hψ₁⟩
    apply isMonHom_of_mul
    intro T x y
    apply ext''
    have e : ∀ z : T ⟶ o₁'.A, pushHom m''.cart T (z ≫ ψ₁) = pushHom m'.cart T z ≫ ψ := by
      intro z
      apply Over.OverMorphism.ext
      rw [p'', Over.comp_left, Over.comp_left, p', Category.assoc, Category.assoc, hψ₁]
    rw [← p'', ← p'', map_mul, e, e, e, map_mul, mul_comp]
  · intro d
    let e : Over.mk (o₁'.A.hom ≫ f) ⟶ o'.A := pushHom m'.cart o₁'.A (𝟙 o₁'.A)
    have h1 : (𝟙 o₁'.A ^ d).left ≫ m'.φ = (e ^ d).left := by
      rw [← p', map_pow]
    have h2 : m'.φ ≫ (𝟙 o'.A ^ d).left = (e ^ d).left := by
      have : e ≫ 𝟙 o'.A ^ d = e ^ d := by rw [comp_pow, Category.comp_id]
      rw [← this, Over.comp_left, p', Over.id_left, Category.id_comp]
    rw [h1, h2]
end

section

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaFEt_of :
    SigmaFEt := by
  intro Y Z s _ _ I _
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k
  let i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y :=
    Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end

section

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private theorem isSquare_square_compatible_homs {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A']
    [IsCommMonObj A'] (ψ : A ⟶ A') : Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.LocalSmoothExtension.polPull_of :
    PolPull := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hc c ⟨h⟩
  letI := o'.grp
  letI := o'.comm
  letI := o''.grp
  letI := o''.comm
  letI := o₁'.grp
  letI := o₁'.comm
  letI := o₁''.grp
  letI := o₁''.comm
  have hsq : Hecke.sq2 ψ₁ ≫ m''.φ₂ = m'.φ₂ ≫ Hecke.sq2 ψ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp (isSquare_square_compatible_homs ψ₁) m''.sq)
    rw [hc]
    exact MapComp.isSquare_comp m'.sq (isSquare_square_compatible_homs ψ)
  have hp : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
  have hp₁ : (Hecke.lbPow o₁'.P c).IsLB := LB.isLB_linComb o₁'.isLB _ _
  have hq : (o''.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o''.isLB _
  have hA := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
  have hB := (GlobalTheory.CechPic.cls_eq_iff o₁''.isLB (pull_isLB o''.isLB m''.φ₂)).2 m''.pol
  have hC := (GlobalTheory.CechPic.cls_eq_iff hp hq).2 h
  refine ⟨(GlobalTheory.CechPic.cls_eq_iff hp₁ (pull_isLB o₁''.isLB _)).1 ?_⟩
  rw [GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB, hA, GlobalTheory.CechPic.cls_pull o'.isLB,
    GlobalTheory.CechPic.cls_pull o₁''.isLB, hB, GlobalTheory.CechPic.cls_pull o''.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
    GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o''.isLB (Hecke.sq2 ψ) hq, ← hC,
    GlobalTheory.BirigidPow.cls_lbPow o'.isLB, map_nsmul]
end

section

open UpperTheory.Gal.LocalSmoothExtension

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem sim_herm {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β u : G.Cˣ) (s : ℚ)
    (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) :
    (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
      (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
  set a : G.C := algebraMap ℚ G.C s with ha
  have hcomm : ∀ x : G.C, a * x = x * a := fun x => Algebra.commutes s x
  have hsh : sh G (u : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) := by
    rw [← hy]
    simp [mul_assoc]
  have key : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C) = a * ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [hsh]
    calc ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C)
        = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * (u : G.C)) := by
          simp [mul_assoc]
      _ = ((β⁻¹ : G.Cˣ) : G.C) * (((u⁻¹ : G.Cˣ) : G.C) * (u : G.C)) * a := by
          rw [hcomm]; simp only [mul_assoc]
      _ = a * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [hcomm]; simp
  have hpa : G.psi v a = (s : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [ha, IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hΓ : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v))
  have hUΓ : (G.psi v (u : G.C))ᴴ * G.gram v = G.gram v * G.psi v (sh G (u : G.C)) := by
    rw [show sh G (u : G.C) = MulOpposite.unop (G.star (u : G.C)) from rfl, G.psi_star]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hΓ, Matrix.one_mul]
  calc (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C))) := by
        rw [map_mul, map_mul, ← Matrix.mul_assoc, hUΓ]
        simp only [Matrix.mul_assoc]
    _ = (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [key, map_mul, hpa, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

private theorem coeff_zero_ne {F A : Type} [Field F] [Ring A] [Algebra F A] [Algebra.IsIntegral F A] [Nontrivial A]
    (g : Aˣ) : (minpoly F (g : A)).coeff 0 ≠ 0 := by
  intro h
  have hint : IsIntegral F (g : A) := Algebra.IsIntegral.isIntegral _
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h
  have hmon : (minpoly F (g : A)).Monic := minpoly.monic hint
  have hqmon : q.Monic := by
    rw [hq] at hmon
    exact Polynomial.monic_X.of_mul_monic_left hmon
  have haeval : Polynomial.aeval (g : A) q = 0 := by
    have h0 := minpoly.aeval F (g : A)
    rw [hq, map_mul, Polynomial.aeval_X] at h0
    have := congrArg (fun y => ((g⁻¹ : Aˣ) : A) * y) h0
    simpa [← mul_assoc] using this
  have hle := minpoly.min F (g : A) hqmon haeval
  rw [hq, Polynomial.degree_mul, Polynomial.degree_X] at hle
  have hq0 : q ≠ 0 := hqmon.ne_zero
  rw [Polynomial.degree_eq_natDegree hq0] at hle
  norm_cast at hle
  omega

theorem dPairPol_of :
    DPairPol := by
  intro p _ G P v
  refine ⟨coeff_zero_ne (F := G.F) (A := G.C) P.γ, (P.c : ℚ), ?_⟩
  intro z hz
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hev : eval₂ v.embedding z (minpoly G.F (P.γ : G.C)) = 0 :=
    (Polynomial.mem_roots_map (minpoly.ne_zero hint)).mp hz
  obtain ⟨x, hx, hMx⟩ := PolyArch.roots_eig_any p G v (P.γ : G.C) z hev
  have hsim := sim_herm G v P.β P.γ (P.c : ℚ) P.sim
  have hform := GlobalTheory.EigenvalueNormSignature.form_mulVec (G.psi v (P.γ : G.C))
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x
  rw [hsim, hMx] at hform
  have hQ : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := P.posR v x hx
    rw [h0] at h1 h2
    simp at h1 h2
    exact h1 h2
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hform
  apply mul_right_cancel₀ hQ
  rw [Complex.star_def] at hform
  push_cast at hform ⊢
  linear_combination hform

end UpperTheory.Gal.LocalSmoothExtension
end

section

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits

private lemma UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaSplit_of :
    SigmaFEt → UpperTheory.Gal.G3.SplitsPts → UpperTheory.Gal.G3.PtsOfSplits → SigmaSplit := by
  intro hF hSP hPS Y Z W s _ _ I _ c Δ _ σ hs
  obtain ⟨hF1, hF2⟩ := hF Y Z s I
  obtain ⟨hsc, hiso⟩ := hs
  have hne : ∀ (Ω : Type) [Field Ω], Nonempty (UpperTheory.Gal.G3.sp Ω) := fun Ω _ =>
    inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hpt : ∀ (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ fun _ : I => Y),
      ∃ i : I, ∃ y' : UpperTheory.Gal.G3.sp Ω ⟶ Y, y' ≫ Sigma.ι (fun _ : I => Y) i = y := by
    intro Ω _ y
    haveI := UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton Ω
    obtain ⟨p⟩ := hne Ω
    obtain ⟨⟨i, a⟩, ha⟩ := (sigmaMk (fun _ : I => Y)).surjective (y.base p)
    rw [sigmaMk_mk] at ha
    refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) i) y ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    exact ⟨a, by rw [Subsingleton.elim q p]; exact ha⟩
  refine hSP _ c (I × Δ) _ ?_ ?_
  · intro z
    simp [hsc]
  · intro Ω _ _ x y hy
    obtain ⟨i, y', rfl⟩ := hpt Ω y
    have hy' : y' ≫ s = x ≫ c := by simpa using hy
    obtain ⟨δ, hδ, hδu⟩ := hPS s c Δ σ ⟨hsc, hiso⟩ Ω x y' hy'
    refine ⟨(i, δ), ?_, ?_⟩
    · show x ≫ (σ δ ≫ _) = _
      rw [← hδ, Category.assoc]
    · rintro ⟨i', δ'⟩ h
      change x ≫ (σ δ' ≫ Sigma.ι (fun _ : I => Y) i') = y' ≫ Sigma.ι (fun _ : I => Y) i at h
      by_cases hii : i' = i
      · subst hii
        have hx : x ≫ σ δ' = y' := by
          rw [← Category.assoc] at h
          exact (cancel_mono _).1 h
        rw [hδu δ' hx]
      · haveI := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) (a := x ≫ σ δ') (b := y')
          ⟨by rw [Category.assoc]; exact h⟩ hii
        obtain ⟨p⟩ := hne Ω
        exact isEmptyElim p
end

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
end

section

open UpperTheory.Gal.LocalSmoothExtension

private theorem exists_perm_of_map_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, b (e i) = a i :=
  _root_.UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq a b h

theorem UpperTheory.Gal.LocalSmoothExtension.schWEq_of :
    SchWEq := by
  intro F _ _ n lam χ g hg
  have h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g := ⟨g, hg⟩
  unfold schW
  rw [dite_eq_left h]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨e, he⟩ := exists_perm_of_map_eq (h.choose τ) (g τ)
    ((h.choose_spec τ).symm.trans (hg τ))
  have hge : h.choose τ = g τ ∘ e := funext fun i => (he i).symm
  rw [hge]
  unfold UpperTheory.Gal.Schur.sch
  rw [← MvPolynomial.aeval_rename, GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric (lam τ) e]
end
