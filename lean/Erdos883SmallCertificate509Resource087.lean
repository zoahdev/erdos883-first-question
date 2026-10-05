import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_87 :
    (List.ofFn coreChunks509_87).flatten =
      (coreData509.take (coreResources509 87).q).drop 210 := by
  decide +kernel

theorem coreCheck509_87 :
    ∀ c : Fin 1, (coreChunks509_87 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 87)) = true := by
  decide +kernel
#print axioms coreFlatten509_87
#print axioms coreCheck509_87
end Erdos883Verified
