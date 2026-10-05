import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_10 :
    (List.ofFn coreChunks509_10).flatten =
      (coreData509.take (coreResources509 10).q).drop 99 := by
  decide +kernel

theorem coreCheck509_10 :
    ∀ c : Fin 1, (coreChunks509_10 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 10)) = true := by
  decide +kernel
#print axioms coreFlatten509_10
#print axioms coreCheck509_10
end Erdos883Verified
