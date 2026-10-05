import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_62 :
    (List.ofFn coreChunks618_62).flatten =
      (coreData618.take (coreResources618 62).q).drop 125 := by
  decide +kernel

theorem coreCheck618_62 :
    ∀ c : Fin 1, (coreChunks618_62 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 62)) = true := by
  decide +kernel
#print axioms coreFlatten618_62
#print axioms coreCheck618_62
end Erdos883Verified
