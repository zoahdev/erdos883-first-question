import Erdos883AdaptiveSpan115021Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_0 : adaptiveNumericSpans115021_0.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_0 : adaptiveSpanEven115021_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_0 : adaptiveSpanEven115021_0.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_0 : adaptiveSpanEven115021_0.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_0 : adaptiveSpanWhole115021_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_0 : adaptiveSpanWhole115021_0.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_0 : adaptiveSpanWhole115021_0.spans = coreWholeSpans 0 adaptiveNumericSpans115021_0 := by
  decide +kernel
end Erdos883Verified
