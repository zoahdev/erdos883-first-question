import Erdos883AdaptiveSpan115021Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_1 : adaptiveNumericSpans115021_1.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_1 : adaptiveSpanEven115021_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_1 : adaptiveSpanEven115021_1.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_1 : adaptiveSpanEven115021_1.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_1 : adaptiveSpanWhole115021_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_1 : adaptiveSpanWhole115021_1.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_1 : adaptiveSpanWhole115021_1.spans = coreWholeSpans 0 adaptiveNumericSpans115021_1 := by
  decide +kernel
end Erdos883Verified
