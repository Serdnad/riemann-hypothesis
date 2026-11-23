module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.GrpBox

open GlobalTheory.SumDeg

theorem isBoxGen_extGen {X X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h₁ : Y ⟶ Y₁) (φ₁ : K → (Y₁ ⟶ X₁)) (e₁ : ∀ k, ψ k ≫ f₁ = h₁ ≫ φ₁ k) (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε))
    (h₂ : Y ⟶ Y₂) (φ₂ : K → (Y₂ ⟶ X₂)) (e₂ : ∀ k, ψ k ≫ f₂ = h₂ ≫ φ₂ k) (t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε))
    (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    IsBoxGen (CubePf.idIsoL (extLB L₁ L₂ f₁ f₂)) h₁ h₂ (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂) t₁ t₂ := by
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  have hE := good_ext (f₁ := f₁) (f₂ := f₂) hJ₁ hJ₂
  have key := gen_trans (isGen_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ ht₁ ht₂) r z (hE.mem ψ r) (hJ.mem ψ r)
  have k2 := gm_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ r z _ (hE.mem ψ r)
  rw [val_of t₁ (r ≫ h₁) z J₁ (fun k => J₁ ((r ≫ ψ k) ≫ f₁)) (fun k => by rw [Category.assoc, Category.assoc, e₁]),
    val_of t₂ (r ≫ h₂) z J₂ (fun k => J₂ ((r ≫ ψ k) ≫ f₂)) (fun k => by rw [Category.assoc, Category.assoc, e₂])]
  exact key.symm.trans k2

section Grp

variable {S : Scheme.{0}} {A A₁ A₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A₁] [IsCommMonObj A₁]
  [GrpObj A₂] [IsCommMonObj A₂]

def pullCub (L : RigLB A₁) (c : CubicalStr A₁ L) (a : A ⟶ A₁) [IsMonHom a] :=
  CubePf.cubical (CubeMap.ofHom a) L c (LB.isLB_pull L.isLB _)
    (LBxP.isGen_pullAlong L.L a.left (𝟙 _) (fun _ : PUnit => eSec A₁) (fun _ => 1)
      (fun _ => eSec A) (fun _ => (CubeMap.ofHom a).e_comm) L.rig L.rigGen)

theorem exists_strBox (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂]
    (L₁ : RigLB A₁) (L₂ : RigLB A₂) (c₁ : CubicalStr A₁ L₁) (c₂ : CubicalStr A₂ L₂)
    (s₁ : SymGen A₁ L₁.L) (s₂ : SymGen A₂ L₂.L) (hs₁ : s₁.IsGen) (hs₂ : s₂.IsGen)
    (n₁ : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec A₁)) (LB.oneGen L₁.L))
    (n₂ : LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec A₂)) (LB.oneGen L₂.L)) :
    ∃ (L : RigLB A) (c : CubicalStr A L) (s : SymGen A L.L)
      (w : LB.Iso L.L (extLB L₁.L L₂.L a₁.left a₂.left)), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L) ∧
      StrBox a₁ a₂ w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  have hL := isLB_extLB L₁.isLB L₂.isLB a₁.left a₂.left
  refine ⟨⟨extLB L₁.L L₂.L a₁.left a₂.left,
      extAt L₁.L L₂.L a₁.left a₂.left (eSec A) 1 _ (eSec_comp a₁) L₁.rig _ (eSec_comp a₂) L₂.rig, hL,
      isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen⟩,
    tensCub (pullCub L₁ c₁ a₁) (pullCub L₂ c₂ a₂) _ hL _,
    extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂,
    CubePf.idIsoL _, isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂, ?_, CubePf.idIsoL_isGen hL,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen,
    isBoxGen_extGen L₁.L L₂.L a₁.left a₂.left (thφ A (x3 A)) thε
      (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (thφ A₁ (x3 A₁)) (fun I => (CubeMap.ofHom a₁).psum_comm I.down) c₁.t
      (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left (thφ A₂ (x3 A₂)) (fun I => (CubeMap.ofHom a₂).psum_comm I.down) c₂.t
      c₁.isGen c₂.isGen,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂⟩
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at L₁.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at L₂.isLB y
  have o : eSec A ≫ (ι[A]).left = eSec A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[A] ≫ ι[A] = η[A])
  have v₁ : val s₁ (eSec A₁) y J₁ = 1 := by
    have v := val_corr hJ₁ n₁ (𝟙 _)
    rwa [val_pull hJ₁, Category.id_comp, val_one] at v
  have v₂ : val s₂ (eSec A₂) y J₂ = 1 := by
    have v := val_corr hJ₂ n₂ (𝟙 _)
    rwa [val_pull hJ₂, Category.id_comp, val_one] at v
  have e := (val_extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂
    hs₁ hs₂ (eSec A) hJ hJ₁ hJ₂).trans (congrArg₂ (· * ·) (prod_sym (eSec A) _) rfl)
  rw [o, mul_inv_cancel, eSec_comp, eSec_comp, v₁, v₂, _root_.mul_one, _root_.mul_one] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

end Grp

theorem exists_prod : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  intro S G₁ G₂ _ _ _ _ L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂
  exact exists_strBox (fst G₁ G₂) (snd G₁ G₂) L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂

end GlobalTheory.GrpBox
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

theorem compat_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {T' T₁' T₂' : Scheme.{0}} {p' : T' ⟶ B} {f' : T' ⟶ G} {p₁' : T₁' ⟶ B₁} {f₁' : T₁' ⟶ G₁} {p₂' : T₂' ⟶ B₂} {f₂' : T₂' ⟶ G₂} {h₁' : T' ⟶ T₁'} {h₂' : T' ⟶ T₂'} (we' : LB.Iso (L.pull f') (M.pull p')) (we₁' : LB.Iso (L₁.pull f₁') (M₁.pull p₁')) (we₂' : LB.Iso (L₂.pull f₂') (M₂.pull p₂')), BoxSq wM wL we' we₁' we₂' h₁' h₂' → ∀ (m : T ⟶ T') (m₁ : T₁ ⟶ T₁') (m₂ : T₂ ⟶ T₂'), m ≫ h₁' = h₁ ≫ m₁ → m ≫ h₂' = h₂ ≫ m₂ → m ≫ f' = f → m ≫ p' = p → m₁ ≫ f₁' = f₁ → m₁ ≫ p₁' = p₁ → m₂ ≫ f₂' = f₂ → m₂ ≫ p₂' = p₂ → GlobalTheory.UnifPullRig.CompatAlong we₁' we₁ m₁ → GlobalTheory.UnifPullRig.CompatAlong we₂' we₂ m₂ → GlobalTheory.UnifPullRig.CompatAlong we' we m := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂ hL hL₁ hL₂
    ep₁ ep₂ ef₁ ef₂ we Q T' T₁' T₂' p' f' p₁' f₁' p₂' f₂' h₁' h₂' we' we₁' we₂' Q' m m₁ m₂ hm₁ hm₂ hmf hmp hm₁f hm₁p
    hm₂f hm₂p H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  have bM : p y ∈ M.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f y ∈ L.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => p) (fun _ => qM ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bM)
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => f) (fun _ => qL ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bL)
  obtain ⟨J₁, hJ₁⟩ := exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := exists_good_at hL₂ y
  have e₀ := Q T (𝟙 T) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have e₁ := Q' T m y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have c₁ := H₁.stalk hm₁f hm₁p h₁ y (J₁ (p ≫ b₁)) (N₁ (f ≫ g₁))
    ((pt_of_eq ep₁ y) ▸ hJ₁ (p ≫ b₁)) ((pt_of_eq ef₁ y) ▸ hN₁ (f ≫ g₁))
  have c₂ := H₂.stalk hm₂f hm₂p h₂ y (J₂ (p ≫ b₂)) (N₂ (f ≫ g₂))
    ((pt_of_eq ep₂ y) ▸ hJ₂ (p ≫ b₂)) ((pt_of_eq ef₂ y) ▸ hN₂ (f ≫ g₂))
  simp only [Category.id_comp] at e₀
  rw [hmp, hmf, hm₁, hm₂, c₁, c₂, ← e₀] at e₁
  have e := mul_left_cancel e₁
  rw [eJ ⟨⟩, eN ⟨⟩] at e
  exact (gm_res_pull _ m y a₁ hy _).trans ((Category.id_comp m).symm ▸ e.trans (gm_res _ y a₂ hy _).symm)

end GlobalTheory.ProdUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open GlobalTheory.UnifPullRig

theorem rigAlong_box : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {S S₀ : Scheme.{0}} (u : S ⟶ T) (u₁ : S ⟶ T₁) (u₂ : S ⟶ T₂) (s : S ⟶ S₀) {eG : S₀ ⟶ G} {eG₁ : S₀ ⟶ G₁} {eG₂ : S₀ ⟶ G₂} {eB : S₀ ⟶ B} {eB₁ : S₀ ⟶ B₁} {eB₂ : S₀ ⟶ B₂} (rL : LB.Gen (L.pull eG)) (rL₁ : LB.Gen (L₁.pull eG₁)) (rL₂ : LB.Gen (L₂.pull eG₂)) (rM : LB.Gen (M.pull eB)) (rM₁ : LB.Gen (M₁.pull eB₁)) (rM₂ : LB.Gen (M₂.pull eB₂)), u ≫ h₁ = u₁ → u ≫ h₂ = u₂ → u ≫ f = s ≫ eG → u ≫ p = s ≫ eB → u₁ ≫ f₁ = s ≫ eG₁ → u₁ ≫ p₁ = s ≫ eB₁ → u₂ ≫ f₂ = s ≫ eG₂ → u₂ ≫ p₂ = s ≫ eB₂ → IsBoxGen wL (𝟙 S₀) (𝟙 S₀) rL rL₁ rL₂ → IsBoxGen wM (𝟙 S₀) (𝟙 S₀) rM rM₁ rM₂ → GlobalTheory.UnifPullRig.RigAlong we₁ u₁ s rL₁ rM₁ → GlobalTheory.UnifPullRig.RigAlong we₂ u₂ s rL₂ rM₂ → GlobalTheory.UnifPullRig.RigAlong we u s rL rM := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂
    hL hL₁ hL₂ hpb₁ hpb₂ hfg₁ hfg₂ we hQ S S₀ u u₁ u₂ s eG eG₁ eG₂ eB eB₁ eB₂ rL rL₁ rL₂ rM rM₁ rM₂ hu₁ hu₂
    hf hp hf₁ hp₁ hf₂ hp₂ bL bM H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => s ≫ eB) (fun _ => qM ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eB) (x := s y)).1 (a₃ hy))
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => s ≫ eG) (fun _ => qL ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eG) (x := s y)).1 (a₂ hy))
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at hL₂ y
  have m₁ : (u ≫ p) ≫ b₁ = s ≫ eB₁ := by rw [Category.assoc, hpb₁, ← Category.assoc, hu₁, hp₁]
  have m₂ : (u ≫ p) ≫ b₂ = s ≫ eB₂ := by rw [Category.assoc, hpb₂, ← Category.assoc, hu₂, hp₂]
  have n₁ : (u ≫ f) ≫ g₁ = s ≫ eG₁ := by rw [Category.assoc, hfg₁, ← Category.assoc, hu₁, hf₁]
  have n₂ : (u ≫ f) ≫ g₂ = s ≫ eG₂ := by rw [Category.assoc, hfg₂, ← Category.assoc, hu₂, hf₂]
  have Q := hQ S u y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  rw [m₁, m₂, n₁, n₂, hu₁, hu₂, hp, hf] at Q
  have HM := bM S s y J₁ J₂ J hJ₁ hJ₂ hJ
  have HL := bL S s y N₁ N₂ N hN₁ hN₂ hN
  simp only [Category.comp_id] at HM HL
  have E₁ := H₁.stalk hf₁ hp₁ (𝟙 S) y (J₁ (s ≫ eB₁)) (N₁ (s ≫ eG₁))
    ((pt_of_eq hp₁ y).symm ▸ hJ₁ (s ≫ eB₁)) ((pt_of_eq hf₁ y).symm ▸ hN₁ (s ≫ eG₁))
  have E₂ := H₂.stalk hf₂ hp₂ (𝟙 S) y (J₂ (s ≫ eB₂)) (N₂ (s ≫ eG₂))
    ((pt_of_eq hp₂ y).symm ▸ hJ₂ (s ≫ eB₂)) ((pt_of_eq hf₂ y).symm ▸ hN₂ (s ≫ eG₂))
  simp only [Category.id_comp] at E₁ E₂
  have key := rel_alg (K := PUnit) (fun _ => 1) (fun _ => om wM y J₁ J₂ J (s ≫ eB))
    (fun _ => om wL y N₁ N₂ N (s ≫ eG)) (fun _ => gw we u y (J (s ≫ eB)) (fun _ => N (s ≫ eG)))
    (fun _ => gw we₁ u₁ y (J₁ (s ≫ eB₁)) (fun _ => N₁ (s ≫ eG₁)))
    (fun _ => gw we₂ u₂ y (J₂ (s ≫ eB₂)) (fun _ => N₂ (s ≫ eG₂))) (fun _ => Q) HM HL
    (by rw [Fintype.prod_unique, zpow_one]; exact E₁.symm) (by rw [Fintype.prod_unique, zpow_one]; exact E₂.symm)
  rw [Fintype.prod_unique, zpow_one, val_of rM s y J qM (fun k => eJ k), val_of rL s y N qL (fun k => eN k),
    eJ ⟨⟩, eN ⟨⟩] at key
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  simp only [Category.id_comp]
  exact key.symm

end GlobalTheory.ProdUnif
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem fam_mul_Oinv {H : Type} [CommGroup H] (Ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → H)
    (α : D.toPre.X) :
    (∏ a, Ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, Ω (Oφl U e α a) ^ Oinvε a =
      Ω (pGl U e) ^ k := by
  have a₀ : (pGl U e) ≫ D.toPre.famφB α 0 = (pGl U e) := Category.comp_id _
  have a₁ : (pGl U e) ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : (pGl U e) ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : (pGl U e) ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = (pGl U e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

theorem sval_eq_sv (σ : H0 U.LG.L k) {Z : Scheme.{0}} (q : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) :
    sval σ q z N = sv U k σ q z (N q) :=
  sval_of σ q z N (fun _ => N q) (fun _ => congrArg N (Category.comp_id _))

end

theorem exp_alg {A X X₁ X₂ : Type} [CommRing A] (k : ℕ) (E : X ≃ X₁ × X₂) (S₁ : Finset X₁) (S₂ : Finset X₂)
    {oM oL W W₁ W₂ : Aˣ} {s s₁ s₂ : A} {f : X → A} {f₁ : X₁ → A} {f₂ : X₂ → A} {t a b : X → Aˣ} {t₁ : X₁ → Aˣ}
    {t₂ : X₂ → Aˣ} (hW : oM * W = W₁ * W₂ * oL) (hs : (oL ^ k).val * s = s₁ * s₂)
    (hf : ∀ x, (a x).val * f x = f₁ (E x).1 * f₂ (E x).2) (ht : ∀ x, b x * t x = t₁ (E x).1 * t₂ (E x).2)
    (ho : ∀ x, a x * b x = oM ^ k) (H₁ : (W₁ ^ k).val * s₁ = ∑ x ∈ S₁, f₁ x * (t₁ x).val)
    (H₂ : (W₂ ^ k).val * s₂ = ∑ x ∈ S₂, f₂ x * (t₂ x).val) :
    (W ^ k).val * s = ∑ x ∈ (S₁ ×ˢ S₂).map E.symm.toEmbedding, f x * (t x).val := by
  refine (oM ^ k).mul_right_inj.1 ?_
  rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul, _root_.mul_assoc, hs, mul_pow,
    Units.val_mul, _root_.mul_mul_mul_comm, H₁, H₂, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_map,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨y, rfl⟩ := E.surjective x
  have e₀ : E.symm.toEmbedding (E y) = y := E.symm_apply_apply y
  rw [e₀, _root_.mul_mul_mul_comm, ← hf, ← Units.val_mul, ← ht, ← ho y, Units.val_mul, Units.val_mul,
    _root_.mul_mul_mul_comm]



theorem expandsAt_boxProd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ A U hq wM wL e k hp₁ hp₂ hT hW σ σ₁ σ₂ f f₁ f₂ hσ hf
    hE₁ hE₂
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U₁ e k σ₁ f₁ hE₁
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U₂ e k σ₂ f₂ hE₂
  have hg₁ := thick_fstG I e (fst G₁ G₂)
  have hg₂ := thick_fstG I e (snd G₁ G₂)
  revert hp₁ hp₂ hT hW hg₁ hg₂
  generalize ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left = ρ₁
  generalize ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left = ρ₂
  intro hp₁ hp₂ hT hW hg₁ hg₂
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₁).left at ρ₁
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₂).left at ρ₂
  change pGl U e ≫ p₁.left = ρ₁ ≫ pGl U₁ e at hp₁
  change pGl U e ≫ p₂.left = ρ₂ ≫ pGl U₂ e at hp₂
  change fGl I (G₁ ⊗ G₂) e ≫ (fst G₁ G₂).left = ρ₁ ≫ fGl I G₁ e at hg₁
  change fGl I (G₁ ⊗ G₂) e ≫ (snd G₁ G₂).left = ρ₂ ≫ fGl I G₂ e at hg₂
  let E : D.toPre.X ≃ D₁.toPre.X × D₂.toPre.X := Equiv.ofBijective _ hq
  refine expandsAt_of_val U e k σ f ((S₁ ×ˢ S₂).map E.symm.toEmbedding) fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.toPre.P.isLB y
  have hF : ∀ α, (∏ a, om wM y J₁ J₂ J (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a).val *
      sval (f α) (pGl U e) y J =
      sval (f₁ (E α).1) (ρ₁ ≫ pGl U₁ e) y J₁ * sval (f₂ (E α).2) (ρ₂ ≫ pGl U₂ e) y J₂ := fun α => by
    rw [← hp₁, ← hp₂]
    exact hf α _ (pGl U e) y J₁ J₂ J hJ₁ hJ₂ hJ
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · refine (Units.mul_right_eq_zero _).1 ((hF α).trans ?_)
    by_cases h₁ : (E α).1 ∈ S₁
    · have h₂ : (E α).2 ∉ S₂ := fun h₂ =>
        hα (Finset.mem_map.2 ⟨E α, Finset.mem_product.2 ⟨h₁, h₂⟩, E.symm_apply_apply α⟩)
      rw [(hS₂ _ ρ₂ y J₂ hJ₂).1 _ h₂, mul_zero]
    · rw [(hS₁ _ ρ₁ y J₁ hJ₁).1 _ h₁, zero_mul]
  · obtain ⟨N, hN, eN⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit) (fun _ => fGl I (G₁ ⊗ G₂) e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : N (fGl I (G₁ ⊗ G₂) e) = jL := eN ⟨⟩
    obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at U₁.LG.isLB y
    obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at U₂.LG.isLB y
    have hT' : ∀ α, (∏ a, om wM y J₁ J₂ J (Oφl U e α a) ^ Oinvε a) * val (tG U e α) (𝟙 _) y J =
        val (tG U₁ e (E α).1) ρ₁ y J₁ * val (tG U₂ e (E α).2) ρ₂ y J₂ := fun α => by
      have := hT α _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
      simp only [Category.id_comp] at this
      exact this
    have hW' : om wM y J₁ J₂ J (pGl U e) * wv U e (𝟙 _) y (J (pGl U e)) (N (fGl I (G₁ ⊗ G₂) e)) =
        wv U₁ e ρ₁ y (J₁ (ρ₁ ≫ pGl U₁ e)) (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          wv U₂ e ρ₂ y (J₂ (ρ₂ ≫ pGl U₂ e)) (N₂ (ρ₂ ≫ fGl I G₂ e)) * om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) := by
      have := hW _ (𝟙 _) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at this
      rw [← hp₁, ← hp₂, ← hg₁, ← hg₂]
      exact this
    have hσ' : (om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) ^ k).val *
        sv U k σ (fGl I (G₁ ⊗ G₂) e) y (N (fGl I (G₁ ⊗ G₂) e)) =
        sv U₁ k σ₁ (ρ₁ ≫ fGl I G₁ e) y (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          sv U₂ k σ₂ (ρ₂ ≫ fGl I G₂ e) y (N₂ (ρ₂ ≫ fGl I G₂ e)) := by
      have := hσ _ (fGl I (G₁ ⊗ G₂) e) y N₁ N₂ N hN₁ hN₂ hN
      rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast] at this
      rw [← sval_eq_sv, ← sval_eq_sv, ← sval_eq_sv, ← hg₁, ← hg₂]
      exact this
    exact exp_alg k E S₁ S₂ hW' hσ' hF hT' (fun α => fam_mul_Oinv U e k (om wM y J₁ J₂ J) α)
      ((hS₁ _ ρ₁ y J₁ hJ₁).2 _ (hN₁ (ρ₁ ≫ fGl I G₁ e))) ((hS₂ _ ρ₂ y J₂ hJ₂).2 _ (hN₂ (ρ₂ ≫ fGl I G₂ e)))

end GlobalTheory.ProdUnif
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.VolBr

theorem volGe_of_hilbertSamuel :
    GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.VolGe := by
  intro hHS hAC hNN k _ X _ p D hX L a hNF hSP hSI
  obtain ⟨P, b, s, t, hPL, hG⟩ := GlobalTheory.T.exists_good_hermitian_lineBundle_pair hAC k X p D hX L
  subst hPL
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow hAC k X p D hX P.L P.A a hSI
  obtain ⟨hRL, hRA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  apply GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower k X p D P.L a
  intro ε hε
  have hF1 : (1 : ℝ) ≤ ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hε3 : 0 < ε / 3 := by positivity
  have hlim : ∀ᶠ n : ℕ in atTop, a - ε / 3 < α n / (n : ℝ) ^ (D + 1) :=
    hαlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hnα, hcont⟩ := ((eventually_ge_atTop 1).and
    (hlim.and (GlobalTheory.T.small_section_count_continuous_from_above hHS hAC k X p D hX P b s t hG (ε / 3) hε3))).exists
  have hRn : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hRL
    have h2 := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ 0 1 _ P.A h1 hRA
    simpa using h2
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample hAC hNN k X p D hX P.L P.A n hSP hNF hG.ample hG.nef
  have hstep := GlobalTheory.T.log_card_smallSections_ge_of_shift_nef hHS hAC k X p D hX P b s t hG n 1 _ (α n) t₀ hRn (hα n) ht₀ (ε / 3) hε3
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨m, hm, hm1, hm2⟩ := ((eventually_ge_atTop (max N₀ 1)).and (hstep.and hcont)).exists
  have hmN : N₀ ≤ m := le_of_max_le_left hm
  refine ⟨n * m, le_trans hmN (Nat.le_mul_of_pos_left m hn1), ?_⟩
  have hsm := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P 1 0 P.L hRL 0 (n * m)).2.1
  rw [mul_one, mul_zero] at hsm
  have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG ((n * m : ℕ) : ℤ) 0 1 hAC
  have hnc : (P.L.pow (n * m)).smallSec.ncard = (P.Bl ((n * m : ℕ) : ℤ) 0 1).ncard := by
    rw [Set.ncard_def, Set.ncard_def, hsm]
  refine ⟨Set.encard_lt_top_iff.mp (hsm ▸ Set.encard_lt_top_iff.mpr hfin), ?_⟩
  rw [hnc]
  change _ ≤ P.lc ((n * m : ℕ) : ℤ) 0 1
  have hcast : (m : ℤ) * (n : ℤ) = ((n * m : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mul_one] at hm1
  set F : ℝ := ((D + 1).factorial : ℝ)
  set x : ℝ := (n : ℝ) ^ (D + 1) with hx
  set y : ℝ := (m : ℝ) ^ (D + 1) with hy
  have hx1 : 1 ≤ x := one_le_pow₀ (by exact_mod_cast hn1)
  have hy0 : 0 ≤ y := by positivity
  have hN : ((n * m : ℕ) : ℝ) ^ (D + 1) = x * y := by push_cast; rw [mul_pow]
  rw [mul_pow] at hm2
  rw [hN]
  have hαx : (a - ε / 3) * x ≤ α n := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < x)).mp hnα
    linarith
  have hF0 : 0 < F := by linarith
  have e1 : (a - ε / 3) * x * y / F ≤ α n / F * y := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαx hy0) hF0.le
  have e2 : ε / 3 * (x * y) / F ≤ ε / 3 * (x * y) :=
    div_le_self (by positivity) hF1
  have e3 : ε / 3 * y ≤ ε / 3 * (x * y) := by
    have : y ≤ x * y := le_mul_of_one_le_left hy0 hx1
    exact mul_le_mul_of_nonneg_left this hε3.le
  have e4 : (a / F - ε) * (x * y) = (a - ε / 3) * x * y / F + ε / 3 * (x * y) / F - ε * (x * y) := by
    field_simp
    ring
  linarith [e1, e2, e3, e4, hm1, hm2]

end GlobalTheory.VolBr
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.etaleCoordinates_descend_along_proper_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  first | exact @GlobalTheory.Mum.etale_coord_descend | exact GlobalTheory.Mum.etale_coord_descend | (intros; apply GlobalTheory.Mum.etale_coord_descend <;> assumption)
end
