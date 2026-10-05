import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_18 :
    (List.ofFn coreChunks158_18).flatten =
      (coreData158.take (coreResources158 18).q).drop 37 := by
  decide +kernel

theorem coreCheck158_18 :
    ∀ c : Fin 1, (coreChunks158_18 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 18)) = true := by
  decide +kernel
#print axioms coreFlatten158_18
#print axioms coreCheck158_18
end Erdos883Verified
