import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_34 :
    (List.ofFn coreChunks462_34).flatten =
      (coreData462.take (coreResources462 34).q).drop 76 := by
  decide +kernel

theorem coreCheck462_34 :
    ∀ c : Fin 1, (coreChunks462_34 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 34)) = true := by
  decide +kernel
#print axioms coreFlatten462_34
#print axioms coreCheck462_34
end Erdos883Verified
