import Erdos883AdaptiveSpan20682Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_8 : adaptiveNumericSpans20682_8.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_8 : adaptiveSpanEven20682_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_8 : adaptiveSpanEven20682_8.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_8 : adaptiveSpanEven20682_8.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_8 : adaptiveSpanWhole20682_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_8 : adaptiveSpanWhole20682_8.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_8 : adaptiveSpanWhole20682_8.spans = coreWholeSpans 0 adaptiveNumericSpans20682_8 := by
  decide +kernel
end Erdos883Verified
