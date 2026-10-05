import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_55 :
    (List.ofFn coreChunks509_55).flatten =
      (coreData509.take (coreResources509 55).q).drop 103 := by
  decide +kernel

theorem coreCheck509_55 :
    ∀ c : Fin 1, (coreChunks509_55 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 55)) = true := by
  decide +kernel
#print axioms coreFlatten509_55
#print axioms coreCheck509_55
end Erdos883Verified
