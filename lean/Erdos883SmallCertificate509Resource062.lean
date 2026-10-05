import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_62 :
    (List.ofFn coreChunks509_62).flatten =
      (coreData509.take (coreResources509 62).q).drop 114 := by
  decide +kernel

theorem coreCheck509_62 :
    ∀ c : Fin 1, (coreChunks509_62 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 62)) = true := by
  decide +kernel
#print axioms coreFlatten509_62
#print axioms coreCheck509_62
end Erdos883Verified
