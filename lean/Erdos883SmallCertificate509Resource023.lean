import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_23 :
    (List.ofFn coreChunks509_23).flatten =
      (coreData509.take (coreResources509 23).q).drop 113 := by
  decide +kernel

theorem coreCheck509_23 :
    ∀ c : Fin 1, (coreChunks509_23 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 23)) = true := by
  decide +kernel
#print axioms coreFlatten509_23
#print axioms coreCheck509_23
end Erdos883Verified
