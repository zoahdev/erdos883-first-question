import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_7 :
    (List.ofFn coreChunks158_7).flatten =
      (coreData158.take (coreResources158 7).q).drop 0 := by
  decide +kernel

theorem coreCheck158_7 :
    ∀ c : Fin 2, (coreChunks158_7 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 7)) = true := by
  decide +kernel
#print axioms coreFlatten158_7
#print axioms coreCheck158_7
end Erdos883Verified
