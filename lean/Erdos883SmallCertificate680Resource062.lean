import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_62 :
    (List.ofFn coreChunks680_62).flatten =
      (coreData680.take (coreResources680 62).q).drop 121 := by
  decide +kernel

theorem coreCheck680_62 :
    ∀ c : Fin 1, (coreChunks680_62 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 62)) = true := by
  decide +kernel
#print axioms coreFlatten680_62
#print axioms coreCheck680_62
end Erdos883Verified
