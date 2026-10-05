import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_46 :
    (List.ofFn coreChunks462_46).flatten =
      (coreData462.take (coreResources462 46).q).drop 92 := by
  decide +kernel

theorem coreCheck462_46 :
    ∀ c : Fin 1, (coreChunks462_46 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 46)) = true := by
  decide +kernel
#print axioms coreFlatten462_46
#print axioms coreCheck462_46
end Erdos883Verified
