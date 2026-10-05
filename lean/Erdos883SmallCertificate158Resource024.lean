import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_24 :
    (List.ofFn coreChunks158_24).flatten =
      (coreData158.take (coreResources158 24).q).drop 47 := by
  decide +kernel

theorem coreCheck158_24 :
    ∀ c : Fin 1, (coreChunks158_24 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 24)) = true := by
  decide +kernel
#print axioms coreFlatten158_24
#print axioms coreCheck158_24
end Erdos883Verified
