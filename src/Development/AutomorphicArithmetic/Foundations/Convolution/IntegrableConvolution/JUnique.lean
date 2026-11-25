module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE
import all Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.JGenLinLie

@[expose] public section

open GroundTheory.Automorphic

private theorem UpperTheory.ConvolutionTheory.L1.jUnique_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  apply _root_.UpperTheory.ConvolutionTheory.Dp.capZc_mem_of_e <;> assumption

theorem UpperTheory.ConvolutionTheory.L1.jUnique :
    UpperTheory.ConvolutionTheory.L1.JUnique := by
  intro K _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen K n τ
  refine ⟨⟨j, hj, fun j' hj' => ?_⟩, (UpperTheory.ConvolutionTheory.Dp.capZc K n τ).1⟩
  refine AlgHom.ext fun x => ?_
  exact UpperTheory.ConvolutionTheory.L1.jUnique_mem_of_e (AlgHom.equalizer j' j)
    (fun a b => ((hiff j').1 hj' a b).trans ((hiff j).1 hj a b).symm) x
