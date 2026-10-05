import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_85 :
    (List.ofFn coreChunks509_85).flatten =
      (coreData509.take (coreResources509 85).q).drop 182 := by
  decide +kernel

theorem coreCheck509_85 :
    ∀ c : Fin 1, (coreChunks509_85 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 85)) = true := by
  decide +kernel
#print axioms coreFlatten509_85
#print axioms coreCheck509_85
end Erdos883Verified
