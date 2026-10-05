import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_14 :
    (List.ofFn coreChunks509_14).flatten =
      (coreData509.take (coreResources509 14).q).drop 103 := by
  decide +kernel

theorem coreCheck509_14 :
    ∀ c : Fin 1, (coreChunks509_14 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 14)) = true := by
  decide +kernel
#print axioms coreFlatten509_14
#print axioms coreCheck509_14
end Erdos883Verified
