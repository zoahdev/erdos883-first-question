import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_11 :
    (List.ofFn coreChunks158_11).flatten =
      (coreData158.take (coreResources158 11).q).drop 28 := by
  decide +kernel

theorem coreCheck158_11 :
    ∀ c : Fin 1, (coreChunks158_11 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 11)) = true := by
  decide +kernel
#print axioms coreFlatten158_11
#print axioms coreCheck158_11
end Erdos883Verified
