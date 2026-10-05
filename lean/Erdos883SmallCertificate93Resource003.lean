import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_3 :
    (List.ofFn coreChunks93_3).flatten =
      (coreData93.take (coreResources93 3).q).drop 16 := by
  decide +kernel

theorem coreCheck93_3 :
    ∀ c : Fin 1, (coreChunks93_3 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 3)) = true := by
  decide +kernel
#print axioms coreFlatten93_3
#print axioms coreCheck93_3
end Erdos883Verified
