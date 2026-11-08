import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureTerminal

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open UnifiedEJM.PhysicsEntanglement

theorem nodeIntegerBound0384 : ∀ pen last, terminalScore 384 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 384).parity (tailData 384 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 384 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0277
  · exact terminalBound0283
  · exact terminalBound0277
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0385 : ∀ pen last, terminalScore 385 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 385).parity (tailData 385 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 385 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0763
  · exact terminalBound0764
  · exact terminalBound0765
  · exact terminalBound0766
theorem nodeIntegerBound0386 : ∀ pen last, terminalScore 386 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 386).parity (tailData 386 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 386 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0759
  · exact terminalBound0767
  · exact terminalBound0759
  · exact terminalBound0760
theorem nodeIntegerBound0387 : ∀ pen last, terminalScore 387 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 387).parity (tailData 387 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 387 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0763
  · exact terminalBound0764
  · exact terminalBound0765
  · exact terminalBound0768
theorem nodeIntegerBound0388 : ∀ pen last, terminalScore 388 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 388).parity (tailData 388 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 388 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0757
  · exact terminalBound0758
  · exact terminalBound0759
  · exact terminalBound0760
theorem nodeIntegerBound0389 : ∀ pen last, terminalScore 389 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 389).parity (tailData 389 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 389 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0761
  · exact terminalBound0762
  · exact terminalBound0759
  · exact terminalBound0767
theorem nodeIntegerBound0390 : ∀ pen last, terminalScore 390 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 390).parity (tailData 390 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 390 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0759
  · exact terminalBound0767
  · exact terminalBound0759
  · exact terminalBound0760
theorem nodeIntegerBound0391 : ∀ pen last, terminalScore 391 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 391).parity (tailData 391 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 391 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0769
  · exact terminalBound0770
  · exact terminalBound0771
  · exact terminalBound0772
theorem nodeIntegerBound0392 : ∀ pen last, terminalScore 392 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 392).parity (tailData 392 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 392 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0773
  · exact terminalBound0774
  · exact terminalBound0775
  · exact terminalBound0776
theorem nodeIntegerBound0393 : ∀ pen last, terminalScore 393 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 393).parity (tailData 393 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 393 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0291
  · exact terminalBound0777
  · exact terminalBound0291
  · exact terminalBound0292
theorem nodeIntegerBound0394 : ∀ pen last, terminalScore 394 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 394).parity (tailData 394 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 394 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0769
  · exact terminalBound0770
  · exact terminalBound0771
  · exact terminalBound0778
theorem nodeIntegerBound0395 : ∀ pen last, terminalScore 395 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 395).parity (tailData 395 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 395 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0779
  · exact terminalBound0780
  · exact terminalBound0781
  · exact terminalBound0782
theorem nodeIntegerBound0396 : ∀ pen last, terminalScore 396 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 396).parity (tailData 396 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 396 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0763
  · exact terminalBound0764
  · exact terminalBound0765
  · exact terminalBound0783
theorem nodeIntegerBound0397 : ∀ pen last, terminalScore 397 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 397).parity (tailData 397 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 397 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0771
  · exact terminalBound0778
  · exact terminalBound0771
  · exact terminalBound0772
theorem nodeIntegerBound0398 : ∀ pen last, terminalScore 398 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 398).parity (tailData 398 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 398 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0784
  · exact terminalBound0785
  · exact terminalBound0781
  · exact terminalBound0782
theorem nodeIntegerBound0399 : ∀ pen last, terminalScore 399 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 399).parity (tailData 399 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 399 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0291
  · exact terminalBound0777
  · exact terminalBound0291
  · exact terminalBound0292
theorem nodeIntegerBound0400 : ∀ pen last, terminalScore 400 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 400).parity (tailData 400 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 400 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0773
  · exact terminalBound0774
  · exact terminalBound0775
  · exact terminalBound0786
theorem nodeIntegerBound0401 : ∀ pen last, terminalScore 401 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 401).parity (tailData 401 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 401 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0787
  · exact terminalBound0788
  · exact terminalBound0781
  · exact terminalBound0782
theorem nodeIntegerBound0402 : ∀ pen last, terminalScore 402 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 402).parity (tailData 402 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 402 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0779
  · exact terminalBound0780
  · exact terminalBound0781
  · exact terminalBound0782
theorem nodeIntegerBound0403 : ∀ pen last, terminalScore 403 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 403).parity (tailData 403 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 403 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0789
  · exact terminalBound0790
  · exact terminalBound0781
  · exact terminalBound0782
theorem nodeIntegerBound0404 : ∀ pen last, terminalScore 404 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 404).parity (tailData 404 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 404 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0761
  · exact terminalBound0762
  · exact terminalBound0759
  · exact terminalBound0791
theorem nodeIntegerBound0405 : ∀ pen last, terminalScore 405 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 405).parity (tailData 405 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 405 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0291
  · exact terminalBound0777
  · exact terminalBound0291
  · exact terminalBound0292
theorem nodeIntegerBound0406 : ∀ pen last, terminalScore 406 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 406).parity (tailData 406 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 406 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0792
  · exact terminalBound0793
  · exact terminalBound0794
  · exact terminalBound0795
theorem nodeIntegerBound0407 : ∀ pen last, terminalScore 407 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 407).parity (tailData 407 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 407 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0763
  · exact terminalBound0764
  · exact terminalBound0765
  · exact terminalBound0796
theorem nodeIntegerBound0408 : ∀ pen last, terminalScore 408 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 408).parity (tailData 408 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 408 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0797
  · exact terminalBound0798
  · exact terminalBound0799
  · exact terminalBound0800
theorem nodeIntegerBound0409 : ∀ pen last, terminalScore 409 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 409).parity (tailData 409 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 409 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0763
  · exact terminalBound0764
  · exact terminalBound0765
  · exact terminalBound0801
theorem nodeIntegerBound0410 : ∀ pen last, terminalScore 410 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 410).parity (tailData 410 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 410 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0794
  · exact terminalBound0802
  · exact terminalBound0794
  · exact terminalBound0795
theorem nodeIntegerBound0411 : ∀ pen last, terminalScore 411 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 411).parity (tailData 411 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 411 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0803
  · exact terminalBound0804
  · exact terminalBound0799
  · exact terminalBound0800
theorem nodeIntegerBound0412 : ∀ pen last, terminalScore 412 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 412).parity (tailData 412 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 412 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0304
  · exact terminalBound0805
  · exact terminalBound0304
  · exact terminalBound0305
theorem nodeIntegerBound0413 : ∀ pen last, terminalScore 413 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 413).parity (tailData 413 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 413 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0806
  · exact terminalBound0807
  · exact terminalBound0808
  · exact terminalBound0809
theorem nodeIntegerBound0414 : ∀ pen last, terminalScore 414 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 414).parity (tailData 414 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 414 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0810
  · exact terminalBound0811
  · exact terminalBound0812
  · exact terminalBound0813
theorem nodeIntegerBound0415 : ∀ pen last, terminalScore 415 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 415).parity (tailData 415 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 415 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0815
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0416 : ∀ pen last, terminalScore 416 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 416).parity (tailData 416 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 416 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0817
  · exact terminalBound0818
  · exact terminalBound0819
theorem nodeIntegerBound0417 : ∀ pen last, terminalScore 417 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 417).parity (tailData 417 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 417 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0820
  · exact terminalBound0821
  · exact terminalBound0822
  · exact terminalBound0823
theorem nodeIntegerBound0418 : ∀ pen last, terminalScore 418 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 418).parity (tailData 418 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 418 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0824
  · exact terminalBound0825
  · exact terminalBound0808
  · exact terminalBound0809
theorem nodeIntegerBound0419 : ∀ pen last, terminalScore 419 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 419).parity (tailData 419 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 419 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0373
  · exact terminalBound0826
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0420 : ∀ pen last, terminalScore 420 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 420).parity (tailData 420 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 420 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0828
  · exact terminalBound0829
  · exact terminalBound0830
theorem nodeIntegerBound0421 : ∀ pen last, terminalScore 421 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 421).parity (tailData 421 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 421 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0815
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0422 : ∀ pen last, terminalScore 422 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 422).parity (tailData 422 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 422 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0365
  · exact terminalBound0831
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0423 : ∀ pen last, terminalScore 423 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 423).parity (tailData 423 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 423 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0314
  · exact terminalBound0315
  · exact terminalBound0314
  · exact terminalBound0316
theorem nodeIntegerBound0424 : ∀ pen last, terminalScore 424 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 424).parity (tailData 424 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 424 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0832
  · exact terminalBound0833
  · exact terminalBound0834
  · exact terminalBound0835
theorem nodeIntegerBound0425 : ∀ pen last, terminalScore 425 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 425).parity (tailData 425 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 425 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0832
  · exact terminalBound0833
  · exact terminalBound0834
  · exact terminalBound0836
theorem nodeIntegerBound0426 : ∀ pen last, terminalScore 426 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 426).parity (tailData 426 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 426 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0837
  · exact terminalBound0838
  · exact terminalBound0829
  · exact terminalBound0839
theorem nodeIntegerBound0427 : ∀ pen last, terminalScore 427 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 427).parity (tailData 427 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 427 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0832
  · exact terminalBound0833
  · exact terminalBound0834
  · exact terminalBound0840
theorem nodeIntegerBound0428 : ∀ pen last, terminalScore 428 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 428).parity (tailData 428 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 428 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0810
  · exact terminalBound0811
  · exact terminalBound0812
  · exact terminalBound0841
theorem nodeIntegerBound0429 : ∀ pen last, terminalScore 429 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 429).parity (tailData 429 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 429 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0842
  · exact terminalBound0843
  · exact terminalBound0844
  · exact terminalBound0845
theorem nodeIntegerBound0430 : ∀ pen last, terminalScore 430 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 430).parity (tailData 430 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 430 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0815
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0431 : ∀ pen last, terminalScore 431 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 431).parity (tailData 431 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 431 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0846
  · exact terminalBound0847
  · exact terminalBound0812
  · exact terminalBound0841
theorem nodeIntegerBound0432 : ∀ pen last, terminalScore 432 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 432).parity (tailData 432 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 432 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0323
  · exact terminalBound0848
  · exact terminalBound0323
  · exact terminalBound0324
theorem nodeIntegerBound0433 : ∀ pen last, terminalScore 433 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 433).parity (tailData 433 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 433 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0329
  · exact terminalBound0330
  · exact terminalBound0331
  · exact terminalBound0849
theorem nodeIntegerBound0434 : ∀ pen last, terminalScore 434 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 434).parity (tailData 434 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 434 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0828
  · exact terminalBound0829
  · exact terminalBound0839
theorem nodeIntegerBound0435 : ∀ pen last, terminalScore 435 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 435).parity (tailData 435 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 435 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0365
  · exact terminalBound0831
  · exact terminalBound0814
  · exact terminalBound0815
theorem nodeIntegerBound0436 : ∀ pen last, terminalScore 436 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 436).parity (tailData 436 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 436 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0815
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0437 : ∀ pen last, terminalScore 437 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 437).parity (tailData 437 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 437 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0379
  · exact terminalBound0850
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0438 : ∀ pen last, terminalScore 438 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 438).parity (tailData 438 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 438 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0817
  · exact terminalBound0818
  · exact terminalBound0851
theorem nodeIntegerBound0439 : ∀ pen last, terminalScore 439 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 439).parity (tailData 439 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 439 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0817
  · exact terminalBound0818
  · exact terminalBound0852
theorem nodeIntegerBound0440 : ∀ pen last, terminalScore 440 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 440).parity (tailData 440 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 440 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0331
  · exact terminalBound0849
  · exact terminalBound0331
  · exact terminalBound0340
theorem nodeIntegerBound0441 : ∀ pen last, terminalScore 441 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 441).parity (tailData 441 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 441 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0853
  · exact terminalBound0854
  · exact terminalBound0829
  · exact terminalBound0839
theorem nodeIntegerBound0442 : ∀ pen last, terminalScore 442 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 442).parity (tailData 442 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 442 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0818
  · exact terminalBound0819
  · exact terminalBound0818
  · exact terminalBound0851
theorem nodeIntegerBound0443 : ∀ pen last, terminalScore 443 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 443).parity (tailData 443 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 443 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0828
  · exact terminalBound0829
  · exact terminalBound0839
theorem nodeIntegerBound0444 : ∀ pen last, terminalScore 444 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 444).parity (tailData 444 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 444 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0331
  · exact terminalBound0849
  · exact terminalBound0331
  · exact terminalBound0340
theorem nodeIntegerBound0445 : ∀ pen last, terminalScore 445 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 445).parity (tailData 445 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 445 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0346
  · exact terminalBound0818
  · exact terminalBound0855
theorem nodeIntegerBound0446 : ∀ pen last, terminalScore 446 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 446).parity (tailData 446 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 446 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0853
  · exact terminalBound0856
  · exact terminalBound0857
  · exact terminalBound0858
theorem nodeIntegerBound0447 : ∀ pen last, terminalScore 447 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 447).parity (tailData 447 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 447 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0860
  · exact terminalBound0861
  · exact terminalBound0862
theorem nodeIntegerBound0448 : ∀ pen last, terminalScore 448 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 448).parity (tailData 448 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 448 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0863
  · exact terminalBound0864
  · exact terminalBound0865
theorem nodeIntegerBound0449 : ∀ pen last, terminalScore 449 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 449).parity (tailData 449 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 449 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0829
  · exact terminalBound0866
  · exact terminalBound0857
  · exact terminalBound0858
theorem nodeIntegerBound0450 : ∀ pen last, terminalScore 450 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 450).parity (tailData 450 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 450 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0867
  · exact terminalBound0864
  · exact terminalBound0868
theorem nodeIntegerBound0451 : ∀ pen last, terminalScore 451 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 451).parity (tailData 451 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 451 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0863
  · exact terminalBound0861
  · exact terminalBound0862
theorem nodeIntegerBound0452 : ∀ pen last, terminalScore 452 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 452).parity (tailData 452 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 452 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0853
  · exact terminalBound0856
  · exact terminalBound0857
  · exact terminalBound0858
theorem nodeIntegerBound0453 : ∀ pen last, terminalScore 453 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 453).parity (tailData 453 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 453 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0828
  · exact terminalBound0857
  · exact terminalBound0869
theorem nodeIntegerBound0454 : ∀ pen last, terminalScore 454 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 454).parity (tailData 454 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 454 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0829
  · exact terminalBound0866
  · exact terminalBound0857
  · exact terminalBound0858
theorem nodeIntegerBound0455 : ∀ pen last, terminalScore 455 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 455).parity (tailData 455 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 455 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0870
  · exact terminalBound0857
  · exact terminalBound0858
theorem nodeIntegerBound0456 : ∀ pen last, terminalScore 456 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 456).parity (tailData 456 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 456 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0331
  · exact terminalBound0348
  · exact terminalBound0349
  · exact terminalBound0350
theorem nodeIntegerBound0457 : ∀ pen last, terminalScore 457 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 457).parity (tailData 457 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 457 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0817
  · exact terminalBound0818
  · exact terminalBound0871
theorem nodeIntegerBound0458 : ∀ pen last, terminalScore 458 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 458).parity (tailData 458 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 458 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0824
  · exact terminalBound0825
  · exact terminalBound0808
  · exact terminalBound0809
theorem nodeIntegerBound0459 : ∀ pen last, terminalScore 459 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 459).parity (tailData 459 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 459 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0872
  · exact terminalBound0873
  · exact terminalBound0822
  · exact terminalBound0874
theorem nodeIntegerBound0460 : ∀ pen last, terminalScore 460 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 460).parity (tailData 460 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 460 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0815
  · exact terminalBound0814
  · exact terminalBound0816
theorem nodeIntegerBound0461 : ∀ pen last, terminalScore 461 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 461).parity (tailData 461 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 461 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0824
  · exact terminalBound0825
  · exact terminalBound0875
  · exact terminalBound0876
theorem nodeIntegerBound0462 : ∀ pen last, terminalScore 462 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 462).parity (tailData 462 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 462 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0877
  · exact terminalBound0878
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0463 : ∀ pen last, terminalScore 463 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 463).parity (tailData 463 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 463 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0881
  · exact terminalBound0861
  · exact terminalBound0882
theorem nodeIntegerBound0464 : ∀ pen last, terminalScore 464 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 464).parity (tailData 464 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 464 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0808
  · exact terminalBound0883
  · exact terminalBound0884
  · exact terminalBound0885
theorem nodeIntegerBound0465 : ∀ pen last, terminalScore 465 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 465).parity (tailData 465 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 465 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0886
  · exact terminalBound0887
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0466 : ∀ pen last, terminalScore 466 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 466).parity (tailData 466 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 466 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0888
  · exact terminalBound0358
  · exact terminalBound0359
theorem nodeIntegerBound0467 : ∀ pen last, terminalScore 467 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 467).parity (tailData 467 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 467 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0360
  · exact terminalBound0818
  · exact terminalBound0889
theorem nodeIntegerBound0468 : ∀ pen last, terminalScore 468 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 468).parity (tailData 468 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 468 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0890
  · exact terminalBound0891
  · exact terminalBound0892
theorem nodeIntegerBound0469 : ∀ pen last, terminalScore 469 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 469).parity (tailData 469 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 469 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0872
  · exact terminalBound0893
  · exact terminalBound0822
  · exact terminalBound0894
theorem nodeIntegerBound0470 : ∀ pen last, terminalScore 470 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 470).parity (tailData 470 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 470 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0895
  · exact terminalBound0896
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0471 : ∀ pen last, terminalScore 471 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 471).parity (tailData 471 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 471 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0890
  · exact terminalBound0864
  · exact terminalBound0897
theorem nodeIntegerBound0472 : ∀ pen last, terminalScore 472 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 472).parity (tailData 472 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 472 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0877
  · exact terminalBound0878
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0473 : ∀ pen last, terminalScore 473 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 473).parity (tailData 473 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 473 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0872
  · exact terminalBound0893
  · exact terminalBound0898
  · exact terminalBound0899
theorem nodeIntegerBound0474 : ∀ pen last, terminalScore 474 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 474).parity (tailData 474 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 474 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0888
  · exact terminalBound0358
  · exact terminalBound0359
theorem nodeIntegerBound0475 : ∀ pen last, terminalScore 475 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 475).parity (tailData 475 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 475 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0900
  · exact terminalBound0829
  · exact terminalBound0901
theorem nodeIntegerBound0476 : ∀ pen last, terminalScore 476 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 476).parity (tailData 476 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 476 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0902
  · exact terminalBound0903
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0477 : ∀ pen last, terminalScore 477 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 477).parity (tailData 477 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 477 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0900
  · exact terminalBound0857
  · exact terminalBound0904
theorem nodeIntegerBound0478 : ∀ pen last, terminalScore 478 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 478).parity (tailData 478 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 478 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0888
  · exact terminalBound0358
  · exact terminalBound0359
theorem nodeIntegerBound0479 : ∀ pen last, terminalScore 479 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 479).parity (tailData 479 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 479 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0342
  · exact terminalBound0369
  · exact terminalBound0818
  · exact terminalBound0905
theorem nodeIntegerBound0480 : ∀ pen last, terminalScore 480 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 480).parity (tailData 480 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 480 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0853
  · exact terminalBound0906
  · exact terminalBound0907
  · exact terminalBound0908
theorem nodeIntegerBound0481 : ∀ pen last, terminalScore 481 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 481).parity (tailData 481 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 481 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0881
  · exact terminalBound0909
  · exact terminalBound0910
theorem nodeIntegerBound0482 : ∀ pen last, terminalScore 482 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 482).parity (tailData 482 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 482 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0881
  · exact terminalBound0891
  · exact terminalBound0911
theorem nodeIntegerBound0483 : ∀ pen last, terminalScore 483 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 483).parity (tailData 483 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 483 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0829
  · exact terminalBound0901
  · exact terminalBound0907
  · exact terminalBound0908
theorem nodeIntegerBound0484 : ∀ pen last, terminalScore 484 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 484).parity (tailData 484 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 484 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0820
  · exact terminalBound0912
  · exact terminalBound0898
  · exact terminalBound0913
theorem nodeIntegerBound0485 : ∀ pen last, terminalScore 485 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 485).parity (tailData 485 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 485 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0877
  · exact terminalBound0914
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0486 : ∀ pen last, terminalScore 486 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 486).parity (tailData 486 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 486 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0859
  · exact terminalBound0881
  · exact terminalBound0864
  · exact terminalBound0915
theorem nodeIntegerBound0487 : ∀ pen last, terminalScore 487 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 487).parity (tailData 487 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 487 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0822
  · exact terminalBound0916
  · exact terminalBound0898
  · exact terminalBound0913
theorem nodeIntegerBound0488 : ∀ pen last, terminalScore 488 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 488).parity (tailData 488 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 488 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0824
  · exact terminalBound0917
  · exact terminalBound0808
  · exact terminalBound0883
theorem nodeIntegerBound0489 : ∀ pen last, terminalScore 489 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 489).parity (tailData 489 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 489 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0877
  · exact terminalBound0914
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0490 : ∀ pen last, terminalScore 490 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 490).parity (tailData 490 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 490 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0824
  · exact terminalBound0917
  · exact terminalBound0884
  · exact terminalBound0885
theorem nodeIntegerBound0491 : ∀ pen last, terminalScore 491 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 491).parity (tailData 491 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 491 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0373
  · exact terminalBound0374
  · exact terminalBound0358
  · exact terminalBound0359
theorem nodeIntegerBound0492 : ∀ pen last, terminalScore 492 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 492).parity (tailData 492 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 492 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0827
  · exact terminalBound0900
  · exact terminalBound0907
  · exact terminalBound0908
theorem nodeIntegerBound0493 : ∀ pen last, terminalScore 493 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 493).parity (tailData 493 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 493 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0829
  · exact terminalBound0901
  · exact terminalBound0907
  · exact terminalBound0908
theorem nodeIntegerBound0494 : ∀ pen last, terminalScore 494 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 494).parity (tailData 494 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 494 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0886
  · exact terminalBound0887
  · exact terminalBound0879
  · exact terminalBound0880
theorem nodeIntegerBound0495 : ∀ pen last, terminalScore 495 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 495).parity (tailData 495 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 495 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0365
  · exact terminalBound0366
  · exact terminalBound0814
  · exact terminalBound0888
theorem nodeIntegerBound0496 : ∀ pen last, terminalScore 496 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 496).parity (tailData 496 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 496 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0814
  · exact terminalBound0888
  · exact terminalBound0358
  · exact terminalBound0359
theorem nodeIntegerBound0497 : ∀ pen last, terminalScore 497 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 497).parity (tailData 497 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 497 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0388
  · exact terminalBound0389
  · exact terminalBound0918
  · exact terminalBound0919
theorem nodeIntegerBound0498 : ∀ pen last, terminalScore 498 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 498).parity (tailData 498 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 498 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0920
  · exact terminalBound0921
  · exact terminalBound0922
  · exact terminalBound0923
theorem nodeIntegerBound0499 : ∀ pen last, terminalScore 499 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 499).parity (tailData 499 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 499 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0918
  · exact terminalBound0919
  · exact terminalBound0390
  · exact terminalBound0391
theorem nodeIntegerBound0500 : ∀ pen last, terminalScore 500 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 500).parity (tailData 500 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 500 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0924
  · exact terminalBound0925
  · exact terminalBound0922
  · exact terminalBound0923
theorem nodeIntegerBound0501 : ∀ pen last, terminalScore 501 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 501).parity (tailData 501 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 501 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0394
  · exact terminalBound0395
  · exact terminalBound0386
  · exact terminalBound0387
theorem nodeIntegerBound0502 : ∀ pen last, terminalScore 502 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 502).parity (tailData 502 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 502 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound0928
  · exact terminalBound0929
theorem nodeIntegerBound0503 : ∀ pen last, terminalScore 503 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 503).parity (tailData 503 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 503 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound0930
  · exact terminalBound0931
theorem nodeIntegerBound0504 : ∀ pen last, terminalScore 504 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 504).parity (tailData 504 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 504 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0932
  · exact terminalBound0933
  · exact terminalBound0922
  · exact terminalBound0923
theorem nodeIntegerBound0505 : ∀ pen last, terminalScore 505 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 505).parity (tailData 505 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 505 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound0928
  · exact terminalBound0929
theorem nodeIntegerBound0506 : ∀ pen last, terminalScore 506 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 506).parity (tailData 506 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 506 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0920
  · exact terminalBound0921
  · exact terminalBound0922
  · exact terminalBound0923
theorem nodeIntegerBound0507 : ∀ pen last, terminalScore 507 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 507).parity (tailData 507 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 507 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0924
  · exact terminalBound0925
  · exact terminalBound0932
  · exact terminalBound0933
theorem nodeIntegerBound0508 : ∀ pen last, terminalScore 508 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 508).parity (tailData 508 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 508 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0932
  · exact terminalBound0933
  · exact terminalBound0922
  · exact terminalBound0923
theorem nodeIntegerBound0509 : ∀ pen last, terminalScore 509 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 509).parity (tailData 509 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 509 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0934
  · exact terminalBound0935
  · exact terminalBound0936
  · exact terminalBound0937
theorem nodeIntegerBound0510 : ∀ pen last, terminalScore 510 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 510).parity (tailData 510 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 510 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0938
  · exact terminalBound0939
  · exact terminalBound0940
  · exact terminalBound0941
theorem nodeIntegerBound0511 : ∀ pen last, terminalScore 511 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 511).parity (tailData 511 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 511 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0942
  · exact terminalBound0943
  · exact terminalBound0404
  · exact terminalBound0405

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
