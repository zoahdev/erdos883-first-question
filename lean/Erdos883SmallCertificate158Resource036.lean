import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_36 :
    (List.ofFn coreChunks158_36).flatten =
      (coreData158.take (coreResources158 36).q).drop 44 := by
  decide +kernel

theorem coreCheck158_36 :
    ∀ c : Fin 1, (coreChunks158_36 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 36)) = true := by
  decide +kernel
#print axioms coreFlatten158_36
#print axioms coreCheck158_36
end Erdos883Verified
