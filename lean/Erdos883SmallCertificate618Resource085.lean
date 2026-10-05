import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_85 :
    (List.ofFn coreChunks618_85).flatten =
      (coreData618.take (coreResources618 85).q).drop 172 := by
  decide +kernel

theorem coreCheck618_85 :
    ∀ c : Fin 1, (coreChunks618_85 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 85)) = true := by
  decide +kernel
#print axioms coreFlatten618_85
#print axioms coreCheck618_85
end Erdos883Verified
