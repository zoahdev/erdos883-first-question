import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_8 :
    (List.ofFn coreChunks93_8).flatten =
      (coreData93.take (coreResources93 8).q).drop 23 := by
  decide +kernel

theorem coreCheck93_8 :
    ∀ c : Fin 1, (coreChunks93_8 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 8)) = true := by
  decide +kernel
#print axioms coreFlatten93_8
#print axioms coreCheck93_8
end Erdos883Verified
