import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_66 :
    (List.ofFn coreChunks462_66).flatten =
      (coreData462.take (coreResources462 66).q).drop 121 := by
  decide +kernel

theorem coreCheck462_66 :
    ∀ c : Fin 1, (coreChunks462_66 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 66)) = true := by
  decide +kernel
#print axioms coreFlatten462_66
#print axioms coreCheck462_66
end Erdos883Verified
