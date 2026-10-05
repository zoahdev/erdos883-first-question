import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_85 :
    (List.ofFn coreChunks680_85).flatten =
      (coreData680.take (coreResources680 85).q).drop 154 := by
  decide +kernel

theorem coreCheck680_85 :
    ∀ c : Fin 1, (coreChunks680_85 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 85)) = true := by
  decide +kernel
#print axioms coreFlatten680_85
#print axioms coreCheck680_85
end Erdos883Verified
