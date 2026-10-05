import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_3 :
    (List.ofFn coreChunks509_3).flatten =
      (coreData509.take (coreResources509 3).q).drop 62 := by
  decide +kernel

theorem coreCheck509_3 :
    ∀ c : Fin 1, (coreChunks509_3 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 3)) = true := by
  decide +kernel
#print axioms coreFlatten509_3
#print axioms coreCheck509_3
end Erdos883Verified
