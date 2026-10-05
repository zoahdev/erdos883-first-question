import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_79 :
    (List.ofFn coreChunks509_79).flatten =
      (coreData509.take (coreResources509 79).q).drop 156 := by
  decide +kernel

theorem coreCheck509_79 :
    ∀ c : Fin 1, (coreChunks509_79 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 79)) = true := by
  decide +kernel
#print axioms coreFlatten509_79
#print axioms coreCheck509_79
end Erdos883Verified
