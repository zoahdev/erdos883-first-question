import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_63 :
    (List.ofFn coreChunks462_63).flatten =
      (coreData462.take (coreResources462 63).q).drop 118 := by
  decide +kernel

theorem coreCheck462_63 :
    ∀ c : Fin 1, (coreChunks462_63 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 63)) = true := by
  decide +kernel
#print axioms coreFlatten462_63
#print axioms coreCheck462_63
end Erdos883Verified
