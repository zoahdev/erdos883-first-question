import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_1 :
    (List.ofFn coreChunks158_1).flatten =
      (coreData158.take (coreResources158 1).q).drop 18 := by
  decide +kernel

theorem coreCheck158_1 :
    ∀ c : Fin 1, (coreChunks158_1 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 1)) = true := by
  decide +kernel
#print axioms coreFlatten158_1
#print axioms coreCheck158_1
end Erdos883Verified
