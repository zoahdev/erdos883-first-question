import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_12 :
    (List.ofFn coreChunks158_12).flatten =
      (coreData158.take (coreResources158 12).q).drop 29 := by
  decide +kernel

theorem coreCheck158_12 :
    ∀ c : Fin 1, (coreChunks158_12 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 12)) = true := by
  decide +kernel
#print axioms coreFlatten158_12
#print axioms coreCheck158_12
end Erdos883Verified
