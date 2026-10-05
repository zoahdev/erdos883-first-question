import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_74 :
    (List.ofFn coreChunks509_74).flatten =
      (coreData509.take (coreResources509 74).q).drop 139 := by
  decide +kernel

theorem coreCheck509_74 :
    ∀ c : Fin 1, (coreChunks509_74 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 74)) = true := by
  decide +kernel
#print axioms coreFlatten509_74
#print axioms coreCheck509_74
end Erdos883Verified
